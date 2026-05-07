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
v_tail_820_ = lean_ctor_get(v_as_x27_817_, 1);
v_fst_821_ = lean_ctor_get(v_head_819_, 0);
v_snd_822_ = lean_ctor_get(v_head_819_, 1);
lean_inc(v_snd_822_);
lean_inc(v_fst_821_);
v_r_823_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_818_, v_fst_821_, v_snd_822_);
v_as_x27_817_ = v_tail_820_;
v_b_818_ = v_r_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_825_, lean_object* v_b_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_825_, v_b_826_);
lean_dec(v_as_x27_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* v_m_828_, lean_object* v_l_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_829_, v_m_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object* v_m_831_, lean_object* v_l_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(v_m_831_, v_l_832_);
lean_dec(v_l_832_);
return v_res_833_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_unsigned_to_nat(16u);
v___x_898_ = lean_mk_array(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21));
v___x_904_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap(void){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_906_, lean_object* v_m_907_, lean_object* v_a_908_, lean_object* v_b_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_907_, v_a_908_, v_b_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object* v_as_911_, lean_object* v_as_x27_912_, lean_object* v_b_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_912_, v_b_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object* v_as_916_, lean_object* v_as_x27_917_, lean_object* v_b_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_916_, v_as_x27_917_, v_b_918_, v_a_919_);
lean_dec(v_as_x27_917_);
lean_dec(v_as_916_);
return v_res_920_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_921_, lean_object* v_a_922_, lean_object* v_x_923_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_925_, lean_object* v_a_926_, lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_925_, v_a_926_, v_x_927_);
lean_dec(v_x_927_);
lean_dec(v_a_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_930_, lean_object* v_data_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_933_, lean_object* v_a_934_, lean_object* v_b_935_, lean_object* v_x_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_934_, v_b_935_, v_x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_938_, lean_object* v_i_939_, lean_object* v_source_940_, lean_object* v_target_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_939_, v_source_940_, v_target_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object* v_name_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; lean_object* v_env_951_; lean_object* v___x_952_; lean_object* v_toEnvExtension_953_; lean_object* v_asyncMode_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_950_ = lean_st_ref_get(v___y_948_);
v_env_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_950_);
v___x_952_ = l_Lean_errorExplanationExt;
v_toEnvExtension_953_ = lean_ctor_get(v___x_952_, 0);
v_asyncMode_954_ = lean_ctor_get(v_toEnvExtension_953_, 2);
v___x_955_ = lean_box(1);
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_955_, v___x_952_, v_env_951_, v_asyncMode_954_, v___x_956_);
v___x_958_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_957_, v_name_947_);
lean_dec(v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object* v_name_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec(v_name_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object* v_name_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_964_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object* v_name_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v_name_973_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(lean_object* v_msgData_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; lean_object* v_env_989_; lean_object* v___x_990_; lean_object* v_mctx_991_; lean_object* v_lctx_992_; lean_object* v_options_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_988_ = lean_st_ref_get(v___y_986_);
v_env_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_env_989_);
lean_dec(v___x_988_);
v___x_990_ = lean_st_ref_get(v___y_984_);
v_mctx_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_ref(v_mctx_991_);
lean_dec(v___x_990_);
v_lctx_992_ = lean_ctor_get(v___y_983_, 2);
v_options_993_ = lean_ctor_get(v___y_985_, 2);
lean_inc_ref(v_options_993_);
lean_inc_ref(v_lctx_992_);
v___x_994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_994_, 0, v_env_989_);
lean_ctor_set(v___x_994_, 1, v_mctx_991_);
lean_ctor_set(v___x_994_, 2, v_lctx_992_);
lean_ctor_set(v___x_994_, 3, v_options_993_);
v___x_995_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_msgData_982_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(lean_object* v_msgData_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1004_; double v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_float_of_nat(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object* v_cls_1009_, lean_object* v_msg_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_ref_1016_; lean_object* v___x_1017_; lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1062_; 
v_ref_1016_ = lean_ctor_get(v___y_1013_, 5);
v___x_1017_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1062_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1062_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v_traceState_1023_; lean_object* v_env_1024_; lean_object* v_nextMacroScope_1025_; lean_object* v_ngen_1026_; lean_object* v_auxDeclNGen_1027_; lean_object* v_cache_1028_; lean_object* v_messages_1029_; lean_object* v_infoState_1030_; lean_object* v_snapshotTasks_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1061_; 
v___x_1022_ = lean_st_ref_take(v___y_1014_);
v_traceState_1023_ = lean_ctor_get(v___x_1022_, 4);
v_env_1024_ = lean_ctor_get(v___x_1022_, 0);
v_nextMacroScope_1025_ = lean_ctor_get(v___x_1022_, 1);
v_ngen_1026_ = lean_ctor_get(v___x_1022_, 2);
v_auxDeclNGen_1027_ = lean_ctor_get(v___x_1022_, 3);
v_cache_1028_ = lean_ctor_get(v___x_1022_, 5);
v_messages_1029_ = lean_ctor_get(v___x_1022_, 6);
v_infoState_1030_ = lean_ctor_get(v___x_1022_, 7);
v_snapshotTasks_1031_ = lean_ctor_get(v___x_1022_, 8);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1033_ = v___x_1022_;
v_isShared_1034_ = v_isSharedCheck_1061_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snapshotTasks_1031_);
lean_inc(v_infoState_1030_);
lean_inc(v_messages_1029_);
lean_inc(v_cache_1028_);
lean_inc(v_traceState_1023_);
lean_inc(v_auxDeclNGen_1027_);
lean_inc(v_ngen_1026_);
lean_inc(v_nextMacroScope_1025_);
lean_inc(v_env_1024_);
lean_dec(v___x_1022_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1061_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint64_t v_tid_1035_; lean_object* v_traces_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1060_; 
v_tid_1035_ = lean_ctor_get_uint64(v_traceState_1023_, sizeof(void*)*1);
v_traces_1036_ = lean_ctor_get(v_traceState_1023_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_traceState_1023_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1038_ = v_traceState_1023_;
v_isShared_1039_ = v_isSharedCheck_1060_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_traces_1036_);
lean_dec(v_traceState_1023_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1060_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; double v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_1042_ = 0;
v___x_1043_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1044_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1044_, 0, v_cls_1009_);
lean_ctor_set(v___x_1044_, 1, v___x_1040_);
lean_ctor_set(v___x_1044_, 2, v___x_1043_);
lean_ctor_set_float(v___x_1044_, sizeof(void*)*3, v___x_1041_);
lean_ctor_set_float(v___x_1044_, sizeof(void*)*3 + 8, v___x_1041_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*3 + 16, v___x_1042_);
v___x_1045_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_1046_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v_a_1018_);
lean_ctor_set(v___x_1046_, 2, v___x_1045_);
lean_inc(v_ref_1016_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_ref_1016_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_PersistentArray_push___redArg(v_traces_1036_, v___x_1047_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1048_);
v___x_1050_ = v___x_1038_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1048_);
lean_ctor_set_uint64(v_reuseFailAlloc_1059_, sizeof(void*)*1, v_tid_1035_);
v___x_1050_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1050_);
v___x_1052_ = v___x_1033_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_env_1024_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_nextMacroScope_1025_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_ngen_1026_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_auxDeclNGen_1027_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1058_, 5, v_cache_1028_);
lean_ctor_set(v_reuseFailAlloc_1058_, 6, v_messages_1029_);
lean_ctor_set(v_reuseFailAlloc_1058_, 7, v_infoState_1030_);
lean_ctor_set(v_reuseFailAlloc_1058_, 8, v_snapshotTasks_1031_);
v___x_1052_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = lean_st_ref_set(v___y_1014_, v___x_1052_);
v___x_1054_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1054_);
v___x_1056_ = v___x_1020_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object* v_cls_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1063_, v_msg_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object* v_as_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
if (lean_obj_tag(v_as_1074_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v_options_1084_; uint8_t v_hasTrace_1085_; 
v_options_1084_ = lean_ctor_get(v___y_1079_, 2);
v_hasTrace_1085_ = lean_ctor_get_uint8(v_options_1084_, sizeof(void*)*1);
if (v_hasTrace_1085_ == 0)
{
lean_object* v_tail_1086_; 
v_tail_1086_ = lean_ctor_get(v_as_1074_, 1);
lean_inc(v_tail_1086_);
lean_dec_ref(v_as_1074_);
v_as_1074_ = v_tail_1086_;
goto _start;
}
else
{
lean_object* v_head_1088_; lean_object* v_tail_1089_; lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v_inheritedTraceOptions_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_head_1088_ = lean_ctor_get(v_as_1074_, 0);
lean_inc(v_head_1088_);
v_tail_1089_ = lean_ctor_get(v_as_1074_, 1);
lean_inc(v_tail_1089_);
lean_dec_ref(v_as_1074_);
v_fst_1090_ = lean_ctor_get(v_head_1088_, 0);
lean_inc_n(v_fst_1090_, 2);
v_snd_1091_ = lean_ctor_get(v_head_1088_, 1);
lean_inc(v_snd_1091_);
lean_dec(v_head_1088_);
v_inheritedTraceOptions_1092_ = lean_ctor_get(v___y_1079_, 13);
v___x_1093_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1094_ = l_Lean_Name_append(v___x_1093_, v_fst_1090_);
v___x_1095_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1092_, v_options_1084_, v___x_1094_);
lean_dec(v___x_1094_);
if (v___x_1095_ == 0)
{
lean_dec(v_snd_1091_);
lean_dec(v_fst_1090_);
v_as_1074_ = v_tail_1089_;
goto _start;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_snd_1091_);
v___x_1098_ = l_Lean_MessageData_ofFormat(v___x_1097_);
v___x_1099_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_1090_, v___x_1098_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_dec_ref(v___x_1099_);
v_as_1074_ = v_tail_1089_;
goto _start;
}
else
{
lean_dec(v_tail_1089_);
return v___x_1099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object* v_as_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1109_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v_res_1117_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_Lean_maxRecDepthErrorMessage;
v___x_1124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
v___x_1126_ = l_Lean_MessageData_ofFormat(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
v___x_1128_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2));
v___x_1129_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object* v_ref_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_ref_1130_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object* v_env_1138_, lean_object* v_declName_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
uint8_t v___x_1142_; lean_object* v_env_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1142_ = 0;
v_env_1143_ = l_Lean_Environment_setExporting(v_env_1138_, v___x_1142_);
lean_inc(v_declName_1139_);
v___x_1144_ = l_Lean_mkPrivateName(v_env_1143_, v_declName_1139_);
v___x_1145_ = 1;
lean_inc_ref(v_env_1143_);
v___x_1146_ = l_Lean_Environment_contains(v_env_1143_, v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1147_ = l_Lean_privateToUserName(v_declName_1139_);
v___x_1148_ = l_Lean_Environment_contains(v_env_1143_, v___x_1147_, v___x_1145_);
v___x_1149_ = lean_box(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___y_1141_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_env_1143_);
lean_dec(v_declName_1139_);
v___x_1151_ = lean_box(v___x_1146_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v___y_1141_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object* v_env_1153_, lean_object* v_declName_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_1153_, v_declName_1154_, v___y_1155_, v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object* v_x_1158_, lean_object* v___y_1159_){
_start:
{
if (lean_obj_tag(v_x_1158_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; 
v_a_1160_ = lean_ctor_get(v_x_1158_, 0);
lean_inc(v_a_1160_);
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_a_1160_);
lean_ctor_set(v___x_1161_, 1, v___y_1159_);
return v___x_1161_;
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v_x_1158_, 0);
lean_inc(v_a_1162_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_a_1162_);
lean_ctor_set(v___x_1163_, 1, v___y_1159_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object* v_x_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_1164_, v___y_1165_);
lean_dec_ref(v_x_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object* v_env_1167_, lean_object* v_stx_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1167_, v_stx_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
if (lean_obj_tag(v_a_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
v_a_1173_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v___x_1171_, 0);
lean_dec(v_unused_1182_);
v___x_1175_ = v___x_1171_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_box(0);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_a_1173_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_val_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1211_; 
v_val_1183_ = lean_ctor_get(v_a_1172_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_a_1172_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1185_ = v_a_1172_;
v_isShared_1186_ = v_isSharedCheck_1211_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_val_1183_);
lean_dec(v_a_1172_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1211_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_snd_1187_; 
v_snd_1187_ = lean_ctor_get(v_val_1183_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_val_1183_);
if (lean_obj_tag(v_snd_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1197_; 
lean_del_object(v___x_1185_);
v_a_1188_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1171_);
v_a_1189_ = lean_ctor_get(v_snd_1187_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_snd_1187_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1191_ = v_snd_1187_;
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v_snd_1187_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1194_, v_a_1188_);
lean_dec_ref(v___x_1194_);
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1210_; 
v_a_1198_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_a_1198_);
lean_dec_ref(v___x_1171_);
v_a_1199_ = lean_ctor_get(v_snd_1187_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_snd_1187_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1201_ = v_snd_1187_;
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v_snd_1187_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_a_1199_);
v___x_1204_ = v___x_1185_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1206_, v_a_1198_);
lean_dec_ref(v___x_1206_);
return v___x_1207_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_a_1212_ = lean_ctor_get(v___x_1171_, 0);
v_a_1213_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1171_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_inc(v_a_1212_);
lean_dec(v___x_1171_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1212_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object* v_env_1221_, lean_object* v_stx_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_1221_, v_stx_1222_, v___y_1223_, v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object* v_env_1226_, lean_object* v_options_1227_, lean_object* v_currNamespace_1228_, lean_object* v_openDecls_1229_, lean_object* v_n_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = l_Lean_ResolveName_resolveGlobalName(v_env_1226_, v_options_1227_, v_currNamespace_1228_, v_openDecls_1229_, v_n_1230_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object* v_env_1235_, lean_object* v_options_1236_, lean_object* v_currNamespace_1237_, lean_object* v_openDecls_1238_, lean_object* v_n_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_1235_, v_options_1236_, v_currNamespace_1237_, v_openDecls_1238_, v_n_1239_, v___y_1240_, v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_options_1236_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object* v_currNamespace_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_currNamespace_1243_);
lean_ctor_set(v___x_1246_, 1, v___y_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_1247_, v___y_1248_, v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object* v_a_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v_key_1254_; lean_object* v_value_1255_; lean_object* v_tail_1256_; uint8_t v___x_1257_; 
v_key_1254_ = lean_ctor_get(v_x_1252_, 0);
v_value_1255_ = lean_ctor_get(v_x_1252_, 1);
v_tail_1256_ = lean_ctor_get(v_x_1252_, 2);
v___x_1257_ = lean_name_eq(v_key_1254_, v_a_1251_);
if (v___x_1257_ == 0)
{
v_x_1252_ = v_tail_1256_;
goto _start;
}
else
{
lean_object* v___x_1259_; 
lean_inc(v_value_1255_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_value_1255_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object* v_a_1260_, lean_object* v_x_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1260_, v_x_1261_);
lean_dec(v_x_1261_);
lean_dec(v_a_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object* v_m_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_buckets_1265_; lean_object* v___x_1266_; uint64_t v___y_1268_; 
v_buckets_1265_ = lean_ctor_get(v_m_1263_, 1);
v___x_1266_ = lean_array_get_size(v_buckets_1265_);
if (lean_obj_tag(v_a_1264_) == 0)
{
uint64_t v___x_1282_; 
v___x_1282_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_1268_ = v___x_1282_;
goto v___jp_1267_;
}
else
{
uint64_t v_hash_1283_; 
v_hash_1283_ = lean_ctor_get_uint64(v_a_1264_, sizeof(void*)*2);
v___y_1268_ = v_hash_1283_;
goto v___jp_1267_;
}
v___jp_1267_:
{
uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v_fold_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1269_ = 32ULL;
v___x_1270_ = lean_uint64_shift_right(v___y_1268_, v___x_1269_);
v_fold_1271_ = lean_uint64_xor(v___y_1268_, v___x_1270_);
v___x_1272_ = 16ULL;
v___x_1273_ = lean_uint64_shift_right(v_fold_1271_, v___x_1272_);
v___x_1274_ = lean_uint64_xor(v_fold_1271_, v___x_1273_);
v___x_1275_ = lean_uint64_to_usize(v___x_1274_);
v___x_1276_ = lean_usize_of_nat(v___x_1266_);
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_sub(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_usize_land(v___x_1275_, v___x_1278_);
v___x_1280_ = lean_array_uget_borrowed(v_buckets_1265_, v___x_1279_);
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1264_, v___x_1280_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object* v_m_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_1284_, v_a_1285_);
lean_dec(v_a_1285_);
lean_dec_ref(v_m_1284_);
return v_res_1286_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object* v_keys_1287_, lean_object* v_i_1288_, lean_object* v_k_1289_){
_start:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_array_get_size(v_keys_1287_);
v___x_1291_ = lean_nat_dec_lt(v_i_1288_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v_i_1288_);
return v___x_1291_;
}
else
{
lean_object* v_k_x27_1292_; uint8_t v___x_1293_; 
v_k_x27_1292_ = lean_array_fget_borrowed(v_keys_1287_, v_i_1288_);
v___x_1293_ = l_Lean_instBEqExtraModUse_beq(v_k_1289_, v_k_x27_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_i_1288_, v___x_1294_);
lean_dec(v_i_1288_);
v_i_1288_ = v___x_1295_;
goto _start;
}
else
{
lean_dec(v_i_1288_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object* v_keys_1297_, lean_object* v_i_1298_, lean_object* v_k_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_1297_, v_i_1298_, v_k_1299_);
lean_dec_ref(v_k_1299_);
lean_dec_ref(v_keys_1297_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0(void){
_start:
{
size_t v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; 
v___x_1302_ = ((size_t)5ULL);
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_shift_left(v___x_1303_, v___x_1302_);
return v___x_1304_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1(void){
_start:
{
size_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; 
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0);
v___x_1307_ = lean_usize_sub(v___x_1306_, v___x_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object* v_x_1308_, size_t v_x_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1308_) == 0)
{
lean_object* v_es_1311_; lean_object* v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; lean_object* v_j_1316_; lean_object* v___x_1317_; 
v_es_1311_ = lean_ctor_get(v_x_1308_, 0);
v___x_1312_ = lean_box(2);
v___x_1313_ = ((size_t)5ULL);
v___x_1314_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1);
v___x_1315_ = lean_usize_land(v_x_1309_, v___x_1314_);
v_j_1316_ = lean_usize_to_nat(v___x_1315_);
v___x_1317_ = lean_array_get_borrowed(v___x_1312_, v_es_1311_, v_j_1316_);
lean_dec(v_j_1316_);
switch(lean_obj_tag(v___x_1317_))
{
case 0:
{
lean_object* v_key_1318_; uint8_t v___x_1319_; 
v_key_1318_ = lean_ctor_get(v___x_1317_, 0);
v___x_1319_ = l_Lean_instBEqExtraModUse_beq(v_x_1310_, v_key_1318_);
return v___x_1319_;
}
case 1:
{
lean_object* v_node_1320_; size_t v___x_1321_; 
v_node_1320_ = lean_ctor_get(v___x_1317_, 0);
v___x_1321_ = lean_usize_shift_right(v_x_1309_, v___x_1313_);
v_x_1308_ = v_node_1320_;
v_x_1309_ = v___x_1321_;
goto _start;
}
default: 
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
return v___x_1323_;
}
}
}
else
{
lean_object* v_ks_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_ks_1324_ = lean_ctor_get(v_x_1308_, 0);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_1324_, v___x_1325_, v_x_1310_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
size_t v_x_20467__boxed_1330_; uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_x_20467__boxed_1330_ = lean_unbox_usize(v_x_1328_);
lean_dec(v_x_1328_);
v_res_1331_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1327_, v_x_20467__boxed_1330_, v_x_1329_);
lean_dec_ref(v_x_1329_);
lean_dec_ref(v_x_1327_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
uint64_t v___x_1335_; size_t v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = l_Lean_instHashableExtraModUse_hash(v_x_1334_);
v___x_1336_ = lean_uint64_to_usize(v___x_1335_);
v___x_1337_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1333_, v___x_1336_, v_x_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
uint8_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_1338_, v_x_1339_);
lean_dec_ref(v_x_1339_);
lean_dec_ref(v_x_1338_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1));
v___x_1345_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0));
v___x_1346_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1345_, v___x_1344_);
return v___x_1346_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1347_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
return v___x_1351_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1353_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
lean_ctor_set(v___x_1353_, 3, v___x_1352_);
lean_ctor_set(v___x_1353_, 4, v___x_1352_);
lean_ctor_set(v___x_1353_, 5, v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_cls_1365_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_1366_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1367_ = l_Lean_Name_append(v___x_1366_, v_cls_1365_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object* v_mod_1378_, uint8_t v_isMeta_1379_, lean_object* v_hint_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; lean_object* v_env_1389_; uint8_t v_isExporting_1390_; lean_object* v___x_1391_; lean_object* v_env_1392_; lean_object* v___x_1393_; lean_object* v_entry_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1388_ = lean_st_ref_get(v___y_1386_);
v_env_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc_ref(v_env_1389_);
lean_dec(v___x_1388_);
v_isExporting_1390_ = lean_ctor_get_uint8(v_env_1389_, sizeof(void*)*8);
lean_dec_ref(v_env_1389_);
v___x_1391_ = lean_st_ref_get(v___y_1386_);
v_env_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_env_1392_);
lean_dec(v___x_1391_);
v___x_1393_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_1378_);
v_entry_1394_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1394_, 0, v_mod_1378_);
lean_ctor_set_uint8(v_entry_1394_, sizeof(void*)*1, v_isExporting_1390_);
lean_ctor_set_uint8(v_entry_1394_, sizeof(void*)*1 + 1, v_isMeta_1379_);
v___x_1395_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1396_ = lean_box(1);
v___x_1397_ = lean_box(0);
v___x_1440_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1393_, v___x_1395_, v_env_1392_, v___x_1396_, v___x_1397_);
v___x_1441_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_1440_, v_entry_1394_);
lean_dec(v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v_options_1442_; uint8_t v_hasTrace_1443_; 
v_options_1442_ = lean_ctor_get(v___y_1385_, 2);
v_hasTrace_1443_ = lean_ctor_get_uint8(v_options_1442_, sizeof(void*)*1);
if (v_hasTrace_1443_ == 0)
{
lean_dec(v_hint_1380_);
lean_dec(v_mod_1378_);
v___y_1399_ = v___y_1384_;
v___y_1400_ = v___y_1386_;
goto v___jp_1398_;
}
else
{
lean_object* v_inheritedTraceOptions_1444_; lean_object* v_cls_1445_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_inheritedTraceOptions_1444_ = lean_ctor_get(v___y_1385_, 13);
v_cls_1445_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_1465_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
v___x_1466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1444_, v_options_1442_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_hint_1380_);
lean_dec(v_mod_1378_);
v___y_1399_ = v___y_1384_;
v___y_1400_ = v___y_1386_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1467_; lean_object* v___y_1469_; 
v___x_1467_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_1390_ == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21));
v___y_1469_ = v___x_1476_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1477_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22));
v___y_1469_ = v___x_1477_;
goto v___jp_1468_;
}
v___jp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v___y_1469_);
v___x_1470_ = l_Lean_stringToMessageData(v___y_1469_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1467_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
if (v_isMeta_1379_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_1452_ = v___x_1473_;
v___y_1453_ = v___x_1474_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_1452_ = v___x_1473_;
v___y_1453_ = v___x_1475_;
goto v___jp_1451_;
}
}
}
v___jp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1447_);
lean_ctor_set(v___x_1449_, 1, v___y_1448_);
v___x_1450_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1445_, v___x_1449_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref(v___x_1450_);
v___y_1399_ = v___y_1384_;
v___y_1400_ = v___y_1386_;
goto v___jp_1398_;
}
else
{
lean_dec_ref(v_entry_1394_);
return v___x_1450_;
}
}
v___jp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
lean_inc_ref(v___y_1453_);
v___x_1454_ = l_Lean_stringToMessageData(v___y_1453_);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1452_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = l_Lean_MessageData_ofName(v_mod_1378_);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_Name_isAnonymous(v_hint_1380_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_1462_ = l_Lean_MessageData_ofName(v_hint_1380_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___y_1447_ = v___x_1459_;
v___y_1448_ = v___x_1463_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1464_; 
lean_dec(v_hint_1380_);
v___x_1464_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
v___y_1447_ = v___x_1459_;
v___y_1448_ = v___x_1464_;
goto v___jp_1446_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v_entry_1394_);
lean_dec(v_hint_1380_);
lean_dec(v_mod_1378_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
v___jp_1398_:
{
lean_object* v___x_1401_; lean_object* v_toEnvExtension_1402_; lean_object* v_env_1403_; lean_object* v_nextMacroScope_1404_; lean_object* v_ngen_1405_; lean_object* v_auxDeclNGen_1406_; lean_object* v_traceState_1407_; lean_object* v_messages_1408_; lean_object* v_infoState_1409_; lean_object* v_snapshotTasks_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1438_; 
v___x_1401_ = lean_st_ref_take(v___y_1400_);
v_toEnvExtension_1402_ = lean_ctor_get(v___x_1395_, 0);
v_env_1403_ = lean_ctor_get(v___x_1401_, 0);
v_nextMacroScope_1404_ = lean_ctor_get(v___x_1401_, 1);
v_ngen_1405_ = lean_ctor_get(v___x_1401_, 2);
v_auxDeclNGen_1406_ = lean_ctor_get(v___x_1401_, 3);
v_traceState_1407_ = lean_ctor_get(v___x_1401_, 4);
v_messages_1408_ = lean_ctor_get(v___x_1401_, 6);
v_infoState_1409_ = lean_ctor_get(v___x_1401_, 7);
v_snapshotTasks_1410_ = lean_ctor_get(v___x_1401_, 8);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v___x_1401_, 5);
lean_dec(v_unused_1439_);
v___x_1412_ = v___x_1401_;
v_isShared_1413_ = v_isSharedCheck_1438_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snapshotTasks_1410_);
lean_inc(v_infoState_1409_);
lean_inc(v_messages_1408_);
lean_inc(v_traceState_1407_);
lean_inc(v_auxDeclNGen_1406_);
lean_inc(v_ngen_1405_);
lean_inc(v_nextMacroScope_1404_);
lean_inc(v_env_1403_);
lean_dec(v___x_1401_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1438_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_asyncMode_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v_asyncMode_1414_ = lean_ctor_get(v_toEnvExtension_1402_, 2);
v___x_1415_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1395_, v_env_1403_, v_entry_1394_, v_asyncMode_1414_, v___x_1397_);
v___x_1416_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 5, v___x_1416_);
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1418_ = v___x_1412_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_nextMacroScope_1404_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_ngen_1405_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_auxDeclNGen_1406_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_traceState_1407_);
lean_ctor_set(v_reuseFailAlloc_1437_, 5, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1437_, 6, v_messages_1408_);
lean_ctor_set(v_reuseFailAlloc_1437_, 7, v_infoState_1409_);
lean_ctor_set(v_reuseFailAlloc_1437_, 8, v_snapshotTasks_1410_);
v___x_1418_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_mctx_1421_; lean_object* v_zetaDeltaFVarIds_1422_; lean_object* v_postponed_1423_; lean_object* v_diag_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1435_; 
v___x_1419_ = lean_st_ref_set(v___y_1400_, v___x_1418_);
v___x_1420_ = lean_st_ref_take(v___y_1399_);
v_mctx_1421_ = lean_ctor_get(v___x_1420_, 0);
v_zetaDeltaFVarIds_1422_ = lean_ctor_get(v___x_1420_, 2);
v_postponed_1423_ = lean_ctor_get(v___x_1420_, 3);
v_diag_1424_ = lean_ctor_get(v___x_1420_, 4);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v___x_1420_, 1);
lean_dec(v_unused_1436_);
v___x_1426_ = v___x_1420_;
v_isShared_1427_ = v_isSharedCheck_1435_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_diag_1424_);
lean_inc(v_postponed_1423_);
lean_inc(v_zetaDeltaFVarIds_1422_);
lean_inc(v_mctx_1421_);
lean_dec(v___x_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1435_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_mctx_1421_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_zetaDeltaFVarIds_1422_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_postponed_1423_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_diag_1424_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_st_ref_set(v___y_1399_, v___x_1430_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_1480_, lean_object* v_isMeta_1481_, lean_object* v_hint_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_isMeta_boxed_1490_; lean_object* v_res_1491_; 
v_isMeta_boxed_1490_ = lean_unbox(v_isMeta_1481_);
v_res_1491_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_1480_, v_isMeta_boxed_1490_, v_hint_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object* v___x_1492_, lean_object* v_declName_1493_, lean_object* v_as_1494_, size_t v_sz_1495_, size_t v_i_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_lt(v_i_1496_, v_sz_1495_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec(v_declName_1493_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_b_1497_);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; lean_object* v_modules_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v_toImport_1512_; lean_object* v_module_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1507_ = l_Lean_Environment_header(v___x_1492_);
v_modules_1508_ = lean_ctor_get(v___x_1507_, 3);
lean_inc_ref(v_modules_1508_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1510_ = lean_array_uget_borrowed(v_as_1494_, v_i_1496_);
v___x_1511_ = lean_array_get(v___x_1509_, v_modules_1508_, v_a_1510_);
lean_dec_ref(v_modules_1508_);
v_toImport_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_toImport_1512_);
lean_dec(v___x_1511_);
v_module_1513_ = lean_ctor_get(v_toImport_1512_, 0);
lean_inc(v_module_1513_);
lean_dec_ref(v_toImport_1512_);
v___x_1514_ = 0;
lean_inc(v_declName_1493_);
v___x_1515_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1513_, v___x_1514_, v_declName_1493_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; 
lean_dec_ref(v___x_1515_);
v___x_1516_ = lean_box(0);
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1496_, v___x_1517_);
v_i_1496_ = v___x_1518_;
v_b_1497_ = v___x_1516_;
goto _start;
}
else
{
lean_dec(v_declName_1493_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1520_, lean_object* v_declName_1521_, lean_object* v_as_1522_, lean_object* v_sz_1523_, lean_object* v_i_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1523_);
lean_dec(v_sz_1523_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1524_);
lean_dec(v_i_1524_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_1520_, v_declName_1521_, v_as_1522_, v_sz_boxed_1533_, v_i_boxed_1534_, v_b_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_as_1522_);
lean_dec_ref(v___x_1520_);
return v_res_1535_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___x_1539_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0));
v___x_1540_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1539_, v___x_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object* v_declName_1543_, uint8_t v_isMeta_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v_env_1556_; lean_object* v___y_1558_; lean_object* v___x_1571_; 
v___x_1552_ = lean_st_ref_get(v___y_1550_);
v_env_1556_ = lean_ctor_get(v___x_1552_, 0);
lean_inc_ref(v_env_1556_);
lean_dec(v___x_1552_);
v___x_1571_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1556_, v_declName_1543_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref(v_env_1556_);
lean_dec(v_declName_1543_);
goto v___jp_1553_;
}
else
{
lean_object* v_val_1572_; lean_object* v___x_1573_; lean_object* v_modules_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_val_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_val_1572_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = l_Lean_Environment_header(v_env_1556_);
v_modules_1574_ = lean_ctor_get(v___x_1573_, 3);
lean_inc_ref(v_modules_1574_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = lean_array_get_size(v_modules_1574_);
v___x_1576_ = lean_nat_dec_lt(v_val_1572_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_dec_ref(v_modules_1574_);
lean_dec(v_val_1572_);
lean_dec_ref(v_env_1556_);
lean_dec(v_declName_1543_);
goto v___jp_1553_;
}
else
{
lean_object* v___x_1577_; lean_object* v_env_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___y_1582_; 
v___x_1577_ = lean_st_ref_get(v___y_1550_);
v_env_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_env_1578_);
lean_dec(v___x_1577_);
v___x_1579_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
v___x_1580_ = lean_array_fget(v_modules_1574_, v_val_1572_);
lean_dec(v_val_1572_);
lean_dec_ref(v_modules_1574_);
if (v_isMeta_1544_ == 0)
{
lean_dec_ref(v_env_1578_);
v___y_1582_ = v_isMeta_1544_;
goto v___jp_1581_;
}
else
{
uint8_t v___x_1593_; 
lean_inc(v_declName_1543_);
v___x_1593_ = l_Lean_isMarkedMeta(v_env_1578_, v_declName_1543_);
if (v___x_1593_ == 0)
{
v___y_1582_ = v_isMeta_1544_;
goto v___jp_1581_;
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = 0;
v___y_1582_ = v___x_1594_;
goto v___jp_1581_;
}
}
v___jp_1581_:
{
lean_object* v_toImport_1583_; lean_object* v_module_1584_; lean_object* v___x_1585_; 
v_toImport_1583_ = lean_ctor_get(v___x_1580_, 0);
lean_inc_ref(v_toImport_1583_);
lean_dec(v___x_1580_);
v_module_1584_ = lean_ctor_get(v_toImport_1583_, 0);
lean_inc(v_module_1584_);
lean_dec_ref(v_toImport_1583_);
lean_inc(v_declName_1543_);
v___x_1585_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1584_, v___y_1582_, v_declName_1543_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v___x_1585_);
v___x_1586_ = l_Lean_indirectModUseExt;
v___x_1587_ = lean_box(1);
v___x_1588_ = lean_box(0);
lean_inc_ref(v_env_1556_);
v___x_1589_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1579_, v___x_1586_, v_env_1556_, v___x_1587_, v___x_1588_);
v___x_1590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_1589_, v_declName_1543_);
lean_dec(v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3));
v___y_1558_ = v___x_1591_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1592_);
lean_dec_ref(v___x_1590_);
v___y_1558_ = v_val_1592_;
goto v___jp_1557_;
}
}
else
{
lean_dec_ref(v_env_1556_);
lean_dec(v_declName_1543_);
return v___x_1585_;
}
}
}
}
v___jp_1553_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
v___jp_1557_:
{
lean_object* v___x_1559_; size_t v_sz_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1559_ = lean_box(0);
v_sz_1560_ = lean_array_size(v___y_1558_);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_1556_, v_declName_1543_, v___y_1558_, v_sz_1560_, v___x_1561_, v___x_1559_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v_env_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v___x_1562_, 0);
lean_dec(v_unused_1570_);
v___x_1564_ = v___x_1562_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v___x_1562_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1559_);
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1559_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
else
{
return v___x_1562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object* v_declName_1595_, lean_object* v_isMeta_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v_isMeta_boxed_1604_; lean_object* v_res_1605_; 
v_isMeta_boxed_1604_ = lean_unbox(v_isMeta_1596_);
v_res_1605_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_1595_, v_isMeta_boxed_1604_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object* v_as_x27_1606_, lean_object* v_b_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
if (lean_obj_tag(v_as_x27_1606_) == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_b_1607_);
return v___x_1615_;
}
else
{
lean_object* v_head_1616_; lean_object* v_tail_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v_head_1616_ = lean_ctor_get(v_as_x27_1606_, 0);
v_tail_1617_ = lean_ctor_get(v_as_x27_1606_, 1);
v___x_1618_ = 1;
lean_inc(v_head_1616_);
v___x_1619_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_1616_, v___x_1618_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref(v___x_1619_);
v___x_1620_ = lean_box(0);
v_as_x27_1606_ = v_tail_1617_;
v_b_1607_ = v___x_1620_;
goto _start;
}
else
{
return v___x_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1622_, lean_object* v_b_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_1622_, v_b_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v_as_x27_1622_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object* v_env_1632_, lean_object* v_currNamespace_1633_, lean_object* v_openDecls_1634_, lean_object* v_n_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = l_Lean_ResolveName_resolveNamespace(v_env_1632_, v_currNamespace_1633_, v_openDecls_1634_, v_n_1635_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object* v_env_1640_, lean_object* v_currNamespace_1641_, lean_object* v_openDecls_1642_, lean_object* v_n_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_1640_, v_currNamespace_1641_, v_openDecls_1642_, v_n_1643_, v___y_1644_, v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1646_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_box(1);
v___x_1648_ = l_Lean_MessageData_ofFormat(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2));
v___x_1653_ = l_Lean_MessageData_ofFormat(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 0)
{
return v_x_1654_;
}
else
{
lean_object* v_head_1656_; lean_object* v_tail_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1679_; 
v_head_1656_ = lean_ctor_get(v_x_1655_, 0);
v_tail_1657_ = lean_ctor_get(v_x_1655_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1655_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1659_ = v_x_1655_;
v_isShared_1660_ = v_isSharedCheck_1679_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_tail_1657_);
lean_inc(v_head_1656_);
lean_dec(v_x_1655_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1679_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_before_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1677_; 
v_before_1661_ = lean_ctor_get(v_head_1656_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_head_1656_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_head_1656_, 1);
lean_dec(v_unused_1678_);
v___x_1663_ = v_head_1656_;
v_isShared_1664_ = v_isSharedCheck_1677_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_before_1661_);
lean_dec(v_head_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1677_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 7);
lean_ctor_set(v___x_1663_, 1, v___x_1665_);
lean_ctor_set(v___x_1663_, 0, v_x_1654_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_x_1654_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 7);
lean_ctor_set(v___x_1659_, 1, v___x_1668_);
lean_ctor_set(v___x_1659_, 0, v___x_1667_);
v___x_1670_ = v___x_1659_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = l_Lean_MessageData_ofSyntax(v_before_1661_);
v___x_1672_ = l_Lean_indentD(v___x_1671_);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1670_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v_x_1654_ = v___x_1673_;
v_x_1655_ = v_tail_1657_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(lean_object* v_opts_1680_, lean_object* v_opt_1681_){
_start:
{
lean_object* v_name_1682_; lean_object* v_defValue_1683_; lean_object* v_map_1684_; lean_object* v___x_1685_; 
v_name_1682_ = lean_ctor_get(v_opt_1681_, 0);
v_defValue_1683_ = lean_ctor_get(v_opt_1681_, 1);
v_map_1684_ = lean_ctor_get(v_opts_1680_, 0);
v___x_1685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1684_, v_name_1682_);
if (lean_obj_tag(v___x_1685_) == 0)
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_unbox(v_defValue_1683_);
return v___x_1686_;
}
else
{
lean_object* v_val_1687_; 
v_val_1687_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_val_1687_);
lean_dec_ref(v___x_1685_);
if (lean_obj_tag(v_val_1687_) == 1)
{
uint8_t v_v_1688_; 
v_v_1688_ = lean_ctor_get_uint8(v_val_1687_, 0);
lean_dec_ref(v_val_1687_);
return v_v_1688_;
}
else
{
uint8_t v___x_1689_; 
lean_dec(v_val_1687_);
v___x_1689_ = lean_unbox(v_defValue_1683_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(lean_object* v_opts_1690_, lean_object* v_opt_1691_){
_start:
{
uint8_t v_res_1692_; lean_object* v_r_1693_; 
v_res_1692_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_1690_, v_opt_1691_);
lean_dec_ref(v_opt_1691_);
lean_dec_ref(v_opts_1690_);
v_r_1693_ = lean_box(v_res_1692_);
return v_r_1693_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1));
v___x_1698_ = l_Lean_MessageData_ofFormat(v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(lean_object* v_msgData_1699_, lean_object* v_macroStack_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_options_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_options_1703_ = lean_ctor_get(v___y_1701_, 2);
v___x_1704_ = l_Lean_Elab_pp_macroStack;
v___x_1705_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_macroStack_1700_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_msgData_1699_);
return v___x_1706_;
}
else
{
if (lean_obj_tag(v_macroStack_1700_) == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_msgData_1699_);
return v___x_1707_;
}
else
{
lean_object* v_head_1708_; lean_object* v_after_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1724_; 
v_head_1708_ = lean_ctor_get(v_macroStack_1700_, 0);
lean_inc(v_head_1708_);
v_after_1709_ = lean_ctor_get(v_head_1708_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_head_1708_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_head_1708_, 0);
lean_dec(v_unused_1725_);
v___x_1711_ = v_head_1708_;
v_isShared_1712_ = v_isSharedCheck_1724_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_after_1709_);
lean_dec(v_head_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1724_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 7);
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
lean_ctor_set(v___x_1711_, 0, v_msgData_1699_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_msgData_1699_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_msgData_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1716_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_MessageData_ofSyntax(v_after_1709_);
v___x_1719_ = l_Lean_indentD(v___x_1718_);
v_msgData_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1720_, 0, v___x_1717_);
lean_ctor_set(v_msgData_1720_, 1, v___x_1719_);
v___x_1721_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_1720_, v_macroStack_1700_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(lean_object* v_msgData_1726_, lean_object* v_macroStack_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_1726_, v_macroStack_1727_, v___y_1728_);
lean_dec_ref(v___y_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object* v_msg_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_ref_1739_; lean_object* v___x_1740_; lean_object* v_a_1741_; lean_object* v_macroStack_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1753_; 
v_ref_1739_ = lean_ctor_get(v___y_1736_, 5);
v___x_1740_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1731_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v_macroStack_1742_ = lean_ctor_get(v___y_1732_, 1);
v___x_1743_ = l_Lean_Elab_getBetterRef(v_ref_1739_, v_macroStack_1742_);
lean_inc(v_macroStack_1742_);
v___x_1744_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_1741_, v_macroStack_1742_, v___y_1736_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1743_);
lean_ctor_set(v___x_1749_, 1, v_a_1745_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 1);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(lean_object* v_ref_1763_, lean_object* v_msg_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_fileName_1772_; lean_object* v_fileMap_1773_; lean_object* v_options_1774_; lean_object* v_currRecDepth_1775_; lean_object* v_maxRecDepth_1776_; lean_object* v_ref_1777_; lean_object* v_currNamespace_1778_; lean_object* v_openDecls_1779_; lean_object* v_initHeartbeats_1780_; lean_object* v_maxHeartbeats_1781_; lean_object* v_quotContext_1782_; lean_object* v_currMacroScope_1783_; uint8_t v_diag_1784_; lean_object* v_cancelTk_x3f_1785_; uint8_t v_suppressElabErrors_1786_; lean_object* v_inheritedTraceOptions_1787_; lean_object* v_ref_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_fileName_1772_ = lean_ctor_get(v___y_1769_, 0);
v_fileMap_1773_ = lean_ctor_get(v___y_1769_, 1);
v_options_1774_ = lean_ctor_get(v___y_1769_, 2);
v_currRecDepth_1775_ = lean_ctor_get(v___y_1769_, 3);
v_maxRecDepth_1776_ = lean_ctor_get(v___y_1769_, 4);
v_ref_1777_ = lean_ctor_get(v___y_1769_, 5);
v_currNamespace_1778_ = lean_ctor_get(v___y_1769_, 6);
v_openDecls_1779_ = lean_ctor_get(v___y_1769_, 7);
v_initHeartbeats_1780_ = lean_ctor_get(v___y_1769_, 8);
v_maxHeartbeats_1781_ = lean_ctor_get(v___y_1769_, 9);
v_quotContext_1782_ = lean_ctor_get(v___y_1769_, 10);
v_currMacroScope_1783_ = lean_ctor_get(v___y_1769_, 11);
v_diag_1784_ = lean_ctor_get_uint8(v___y_1769_, sizeof(void*)*14);
v_cancelTk_x3f_1785_ = lean_ctor_get(v___y_1769_, 12);
v_suppressElabErrors_1786_ = lean_ctor_get_uint8(v___y_1769_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1787_ = lean_ctor_get(v___y_1769_, 13);
v_ref_1788_ = l_Lean_replaceRef(v_ref_1763_, v_ref_1777_);
lean_inc_ref(v_inheritedTraceOptions_1787_);
lean_inc(v_cancelTk_x3f_1785_);
lean_inc(v_currMacroScope_1783_);
lean_inc(v_quotContext_1782_);
lean_inc(v_maxHeartbeats_1781_);
lean_inc(v_initHeartbeats_1780_);
lean_inc(v_openDecls_1779_);
lean_inc(v_currNamespace_1778_);
lean_inc(v_maxRecDepth_1776_);
lean_inc(v_currRecDepth_1775_);
lean_inc_ref(v_options_1774_);
lean_inc_ref(v_fileMap_1773_);
lean_inc_ref(v_fileName_1772_);
v___x_1789_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1789_, 0, v_fileName_1772_);
lean_ctor_set(v___x_1789_, 1, v_fileMap_1773_);
lean_ctor_set(v___x_1789_, 2, v_options_1774_);
lean_ctor_set(v___x_1789_, 3, v_currRecDepth_1775_);
lean_ctor_set(v___x_1789_, 4, v_maxRecDepth_1776_);
lean_ctor_set(v___x_1789_, 5, v_ref_1788_);
lean_ctor_set(v___x_1789_, 6, v_currNamespace_1778_);
lean_ctor_set(v___x_1789_, 7, v_openDecls_1779_);
lean_ctor_set(v___x_1789_, 8, v_initHeartbeats_1780_);
lean_ctor_set(v___x_1789_, 9, v_maxHeartbeats_1781_);
lean_ctor_set(v___x_1789_, 10, v_quotContext_1782_);
lean_ctor_set(v___x_1789_, 11, v_currMacroScope_1783_);
lean_ctor_set(v___x_1789_, 12, v_cancelTk_x3f_1785_);
lean_ctor_set(v___x_1789_, 13, v_inheritedTraceOptions_1787_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*14, v_diag_1784_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*14 + 1, v_suppressElabErrors_1786_);
v___x_1790_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___x_1789_, v___y_1770_);
lean_dec_ref(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_1791_, v_msg_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v_ref_1791_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v_env_1811_; lean_object* v_options_1812_; lean_object* v_currRecDepth_1813_; lean_object* v_maxRecDepth_1814_; lean_object* v_ref_1815_; lean_object* v_currNamespace_1816_; lean_object* v_openDecls_1817_; lean_object* v_quotContext_1818_; lean_object* v_currMacroScope_1819_; lean_object* v___x_1820_; lean_object* v_nextMacroScope_1821_; lean_object* v___f_1822_; lean_object* v___f_1823_; lean_object* v___f_1824_; lean_object* v___f_1825_; lean_object* v___f_1826_; lean_object* v_methods_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1810_ = lean_st_ref_get(v___y_1808_);
v_env_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc_ref_n(v_env_1811_, 4);
lean_dec(v___x_1810_);
v_options_1812_ = lean_ctor_get(v___y_1807_, 2);
v_currRecDepth_1813_ = lean_ctor_get(v___y_1807_, 3);
v_maxRecDepth_1814_ = lean_ctor_get(v___y_1807_, 4);
v_ref_1815_ = lean_ctor_get(v___y_1807_, 5);
v_currNamespace_1816_ = lean_ctor_get(v___y_1807_, 6);
v_openDecls_1817_ = lean_ctor_get(v___y_1807_, 7);
v_quotContext_1818_ = lean_ctor_get(v___y_1807_, 10);
v_currMacroScope_1819_ = lean_ctor_get(v___y_1807_, 11);
v___x_1820_ = lean_st_ref_get(v___y_1808_);
v_nextMacroScope_1821_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_nextMacroScope_1821_);
lean_dec(v___x_1820_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1822_, 0, v_env_1811_);
v___f_1823_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1823_, 0, v_env_1811_);
lean_inc_n(v_openDecls_1817_, 2);
lean_inc_n(v_currNamespace_1816_, 3);
v___f_1824_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1824_, 0, v_env_1811_);
lean_closure_set(v___f_1824_, 1, v_currNamespace_1816_);
lean_closure_set(v___f_1824_, 2, v_openDecls_1817_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1825_, 0, v_currNamespace_1816_);
lean_inc_ref(v_options_1812_);
v___f_1826_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1826_, 0, v_env_1811_);
lean_closure_set(v___f_1826_, 1, v_options_1812_);
lean_closure_set(v___f_1826_, 2, v_currNamespace_1816_);
lean_closure_set(v___f_1826_, 3, v_openDecls_1817_);
v_methods_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1827_, 0, v___f_1822_);
lean_ctor_set(v_methods_1827_, 1, v___f_1825_);
lean_ctor_set(v_methods_1827_, 2, v___f_1823_);
lean_ctor_set(v_methods_1827_, 3, v___f_1824_);
lean_ctor_set(v_methods_1827_, 4, v___f_1826_);
lean_inc(v_ref_1815_);
lean_inc(v_maxRecDepth_1814_);
lean_inc(v_currRecDepth_1813_);
lean_inc(v_currMacroScope_1819_);
lean_inc(v_quotContext_1818_);
v___x_1828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1828_, 0, v_methods_1827_);
lean_ctor_set(v___x_1828_, 1, v_quotContext_1818_);
lean_ctor_set(v___x_1828_, 2, v_currMacroScope_1819_);
lean_ctor_set(v___x_1828_, 3, v_currRecDepth_1813_);
lean_ctor_set(v___x_1828_, 4, v_maxRecDepth_1814_);
lean_ctor_set(v___x_1828_, 5, v_ref_1815_);
v___x_1829_ = lean_box(0);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v_nextMacroScope_1821_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
lean_ctor_set(v___x_1830_, 2, v___x_1829_);
v___x_1831_ = lean_apply_2(v_x_1802_, v___x_1828_, v___x_1830_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v_a_1833_; lean_object* v_macroScope_1834_; lean_object* v_traceMsgs_1835_; lean_object* v_expandedMacroDecls_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 1);
lean_inc(v_a_1832_);
v_a_1833_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___x_1831_);
v_macroScope_1834_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_macroScope_1834_);
v_traceMsgs_1835_ = lean_ctor_get(v_a_1832_, 1);
lean_inc(v_traceMsgs_1835_);
v_expandedMacroDecls_1836_ = lean_ctor_get(v_a_1832_, 2);
lean_inc(v_expandedMacroDecls_1836_);
lean_dec(v_a_1832_);
v___x_1837_ = lean_box(0);
v___x_1838_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_1836_, v___x_1837_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v_expandedMacroDecls_1836_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; lean_object* v_env_1840_; lean_object* v_ngen_1841_; lean_object* v_auxDeclNGen_1842_; lean_object* v_traceState_1843_; lean_object* v_cache_1844_; lean_object* v_messages_1845_; lean_object* v_infoState_1846_; lean_object* v_snapshotTasks_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v___x_1838_);
v___x_1839_ = lean_st_ref_take(v___y_1808_);
v_env_1840_ = lean_ctor_get(v___x_1839_, 0);
v_ngen_1841_ = lean_ctor_get(v___x_1839_, 2);
v_auxDeclNGen_1842_ = lean_ctor_get(v___x_1839_, 3);
v_traceState_1843_ = lean_ctor_get(v___x_1839_, 4);
v_cache_1844_ = lean_ctor_get(v___x_1839_, 5);
v_messages_1845_ = lean_ctor_get(v___x_1839_, 6);
v_infoState_1846_ = lean_ctor_get(v___x_1839_, 7);
v_snapshotTasks_1847_ = lean_ctor_get(v___x_1839_, 8);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v___x_1839_, 1);
lean_dec(v_unused_1874_);
v___x_1849_ = v___x_1839_;
v_isShared_1850_ = v_isSharedCheck_1873_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snapshotTasks_1847_);
lean_inc(v_infoState_1846_);
lean_inc(v_messages_1845_);
lean_inc(v_cache_1844_);
lean_inc(v_traceState_1843_);
lean_inc(v_auxDeclNGen_1842_);
lean_inc(v_ngen_1841_);
lean_inc(v_env_1840_);
lean_dec(v___x_1839_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1873_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_macroScope_1834_);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_env_1840_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_macroScope_1834_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_ngen_1841_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_auxDeclNGen_1842_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_traceState_1843_);
lean_ctor_set(v_reuseFailAlloc_1872_, 5, v_cache_1844_);
lean_ctor_set(v_reuseFailAlloc_1872_, 6, v_messages_1845_);
lean_ctor_set(v_reuseFailAlloc_1872_, 7, v_infoState_1846_);
lean_ctor_set(v_reuseFailAlloc_1872_, 8, v_snapshotTasks_1847_);
v___x_1852_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_st_ref_set(v___y_1808_, v___x_1852_);
v___x_1854_ = l_List_reverse___redArg(v_traceMsgs_1835_);
v___x_1855_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_1854_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1855_, 0);
lean_dec(v_unused_1863_);
v___x_1857_ = v___x_1855_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_dec(v___x_1855_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v_a_1833_);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1833_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_a_1833_);
v_a_1864_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1855_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1855_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_traceMsgs_1835_);
lean_dec(v_macroScope_1834_);
lean_dec(v_a_1833_);
v_a_1875_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1838_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1838_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; 
v_a_1883_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1831_);
if (lean_obj_tag(v_a_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_a_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_a_1884_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_a_1884_);
v_a_1885_ = lean_ctor_get(v_a_1883_, 1);
lean_inc_ref(v_a_1885_);
lean_dec_ref(v_a_1883_);
v___x_1886_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0));
v___x_1887_ = lean_string_dec_eq(v_a_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_a_1885_);
v___x_1889_ = l_Lean_MessageData_ofFormat(v___x_1888_);
v___x_1890_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_1884_, v___x_1889_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v_a_1884_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; 
lean_dec_ref(v_a_1885_);
v___x_1891_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_1884_);
return v___x_1891_;
}
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_1892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(lean_object* v_t_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v_infoState_1906_; uint8_t v_enabled_1907_; 
v___x_1905_ = lean_st_ref_get(v___y_1903_);
v_infoState_1906_ = lean_ctor_get(v___x_1905_, 7);
lean_inc_ref(v_infoState_1906_);
lean_dec(v___x_1905_);
v_enabled_1907_ = lean_ctor_get_uint8(v_infoState_1906_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1906_);
if (v_enabled_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec_ref(v_t_1902_);
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; lean_object* v_infoState_1911_; lean_object* v_env_1912_; lean_object* v_nextMacroScope_1913_; lean_object* v_ngen_1914_; lean_object* v_auxDeclNGen_1915_; lean_object* v_traceState_1916_; lean_object* v_cache_1917_; lean_object* v_messages_1918_; lean_object* v_snapshotTasks_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1941_; 
v___x_1910_ = lean_st_ref_take(v___y_1903_);
v_infoState_1911_ = lean_ctor_get(v___x_1910_, 7);
v_env_1912_ = lean_ctor_get(v___x_1910_, 0);
v_nextMacroScope_1913_ = lean_ctor_get(v___x_1910_, 1);
v_ngen_1914_ = lean_ctor_get(v___x_1910_, 2);
v_auxDeclNGen_1915_ = lean_ctor_get(v___x_1910_, 3);
v_traceState_1916_ = lean_ctor_get(v___x_1910_, 4);
v_cache_1917_ = lean_ctor_get(v___x_1910_, 5);
v_messages_1918_ = lean_ctor_get(v___x_1910_, 6);
v_snapshotTasks_1919_ = lean_ctor_get(v___x_1910_, 8);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1941_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_snapshotTasks_1919_);
lean_inc(v_infoState_1911_);
lean_inc(v_messages_1918_);
lean_inc(v_cache_1917_);
lean_inc(v_traceState_1916_);
lean_inc(v_auxDeclNGen_1915_);
lean_inc(v_ngen_1914_);
lean_inc(v_nextMacroScope_1913_);
lean_inc(v_env_1912_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1941_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
uint8_t v_enabled_1923_; lean_object* v_assignment_1924_; lean_object* v_lazyAssignment_1925_; lean_object* v_trees_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1940_; 
v_enabled_1923_ = lean_ctor_get_uint8(v_infoState_1911_, sizeof(void*)*3);
v_assignment_1924_ = lean_ctor_get(v_infoState_1911_, 0);
v_lazyAssignment_1925_ = lean_ctor_get(v_infoState_1911_, 1);
v_trees_1926_ = lean_ctor_get(v_infoState_1911_, 2);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_infoState_1911_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1928_ = v_infoState_1911_;
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_trees_1926_);
lean_inc(v_lazyAssignment_1925_);
lean_inc(v_assignment_1924_);
lean_dec(v_infoState_1911_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = l_Lean_PersistentArray_push___redArg(v_trees_1926_, v_t_1902_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 2, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_assignment_1924_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_lazyAssignment_1925_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___x_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1939_, sizeof(void*)*3, v_enabled_1923_);
v___x_1932_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 7, v___x_1932_);
v___x_1934_ = v___x_1921_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_env_1912_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_nextMacroScope_1913_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_ngen_1914_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_auxDeclNGen_1915_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_traceState_1916_);
lean_ctor_set(v_reuseFailAlloc_1938_, 5, v_cache_1917_);
lean_ctor_set(v_reuseFailAlloc_1938_, 6, v_messages_1918_);
lean_ctor_set(v_reuseFailAlloc_1938_, 7, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1938_, 8, v_snapshotTasks_1919_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_st_ref_set(v___y_1903_, v___x_1934_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(lean_object* v_t_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_1942_, v___y_1943_);
lean_dec(v___y_1943_);
return v_res_1945_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_unsigned_to_nat(32u);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1(void){
_start:
{
size_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = ((size_t)5ULL);
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_unsigned_to_nat(32u);
v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1951_);
v___x_1953_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
v___x_1954_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1952_);
lean_ctor_set(v___x_1954_, 2, v___x_1950_);
lean_ctor_set(v___x_1954_, 3, v___x_1950_);
lean_ctor_set_usize(v___x_1954_, 4, v___x_1949_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object* v_t_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; lean_object* v_infoState_1964_; uint8_t v_enabled_1965_; 
v___x_1963_ = lean_st_ref_get(v___y_1961_);
v_infoState_1964_ = lean_ctor_get(v___x_1963_, 7);
lean_inc_ref(v_infoState_1964_);
lean_dec(v___x_1963_);
v_enabled_1965_ = lean_ctor_get_uint8(v_infoState_1964_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1964_);
if (v_enabled_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v_t_1955_);
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_t_1955_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_1969_, v___y_1961_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object* v_t_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v_t_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object* v_info_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_info_1980_);
v___x_1989_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_1988_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object* v_info_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1998_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t v___y_2006_, uint8_t v_suppressElabErrors_2007_, lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 1)
{
lean_object* v_pre_2009_; 
v_pre_2009_ = lean_ctor_get(v_x_2008_, 0);
switch(lean_obj_tag(v_pre_2009_))
{
case 1:
{
lean_object* v_pre_2010_; 
v_pre_2010_ = lean_ctor_get(v_pre_2009_, 0);
switch(lean_obj_tag(v_pre_2010_))
{
case 0:
{
lean_object* v_str_2011_; lean_object* v_str_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_str_2011_ = lean_ctor_get(v_x_2008_, 1);
v_str_2012_ = lean_ctor_get(v_pre_2009_, 1);
v___x_2013_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0));
v___x_2014_ = lean_string_dec_eq(v_str_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1));
v___x_2016_ = lean_string_dec_eq(v_str_2012_, v___x_2015_);
if (v___x_2016_ == 0)
{
return v___y_2006_;
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2));
v___x_2018_ = lean_string_dec_eq(v_str_2011_, v___x_2017_);
if (v___x_2018_ == 0)
{
return v___y_2006_;
}
else
{
return v_suppressElabErrors_2007_;
}
}
}
else
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3));
v___x_2020_ = lean_string_dec_eq(v_str_2011_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___y_2006_;
}
else
{
return v_suppressElabErrors_2007_;
}
}
}
case 1:
{
lean_object* v_pre_2021_; 
v_pre_2021_ = lean_ctor_get(v_pre_2010_, 0);
if (lean_obj_tag(v_pre_2021_) == 0)
{
lean_object* v_str_2022_; lean_object* v_str_2023_; lean_object* v_str_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v_str_2022_ = lean_ctor_get(v_x_2008_, 1);
v_str_2023_ = lean_ctor_get(v_pre_2009_, 1);
v_str_2024_ = lean_ctor_get(v_pre_2010_, 1);
v___x_2025_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4));
v___x_2026_ = lean_string_dec_eq(v_str_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
return v___y_2006_;
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5));
v___x_2028_ = lean_string_dec_eq(v_str_2023_, v___x_2027_);
if (v___x_2028_ == 0)
{
return v___y_2006_;
}
else
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6));
v___x_2030_ = lean_string_dec_eq(v_str_2022_, v___x_2029_);
if (v___x_2030_ == 0)
{
return v___y_2006_;
}
else
{
return v_suppressElabErrors_2007_;
}
}
}
}
else
{
return v___y_2006_;
}
}
default: 
{
return v___y_2006_;
}
}
}
case 0:
{
lean_object* v_str_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_str_2031_ = lean_ctor_get(v_x_2008_, 1);
v___x_2032_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0));
v___x_2033_ = lean_string_dec_eq(v_str_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
return v___y_2006_;
}
else
{
return v_suppressElabErrors_2007_;
}
}
default: 
{
return v___y_2006_;
}
}
}
else
{
return v___y_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v___y_2034_, lean_object* v_suppressElabErrors_2035_, lean_object* v_x_2036_){
_start:
{
uint8_t v___y_21547__boxed_2037_; uint8_t v_suppressElabErrors_boxed_2038_; uint8_t v_res_2039_; lean_object* v_r_2040_; 
v___y_21547__boxed_2037_ = lean_unbox(v___y_2034_);
v_suppressElabErrors_boxed_2038_ = lean_unbox(v_suppressElabErrors_2035_);
v_res_2039_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v___y_21547__boxed_2037_, v_suppressElabErrors_boxed_2038_, v_x_2036_);
lean_dec(v_x_2036_);
v_r_2040_ = lean_box(v_res_2039_);
return v_r_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(lean_object* v_ref_2041_, lean_object* v_msgData_2042_, uint8_t v_severity_2043_, uint8_t v_isSilent_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; uint8_t v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; uint8_t v___y_2092_; uint8_t v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; uint8_t v___y_2116_; uint8_t v___y_2117_; uint8_t v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; uint8_t v___y_2127_; uint8_t v___y_2128_; uint8_t v___y_2129_; uint8_t v___x_2134_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; uint8_t v___y_2141_; uint8_t v___y_2142_; uint8_t v___y_2144_; uint8_t v___x_2159_; 
v___x_2134_ = 2;
v___x_2159_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2043_, v___x_2134_);
if (v___x_2159_ == 0)
{
v___y_2144_ = v___x_2159_;
goto v___jp_2143_;
}
else
{
uint8_t v___x_2160_; 
lean_inc_ref(v_msgData_2042_);
v___x_2160_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2042_);
v___y_2144_ = v___x_2160_;
goto v___jp_2143_;
}
v___jp_2050_:
{
lean_object* v___x_2060_; lean_object* v_currNamespace_2061_; lean_object* v_openDecls_2062_; lean_object* v_env_2063_; lean_object* v_nextMacroScope_2064_; lean_object* v_ngen_2065_; lean_object* v_auxDeclNGen_2066_; lean_object* v_traceState_2067_; lean_object* v_cache_2068_; lean_object* v_messages_2069_; lean_object* v_infoState_2070_; lean_object* v_snapshotTasks_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2085_; 
v___x_2060_ = lean_st_ref_take(v___y_2059_);
v_currNamespace_2061_ = lean_ctor_get(v___y_2058_, 6);
v_openDecls_2062_ = lean_ctor_get(v___y_2058_, 7);
v_env_2063_ = lean_ctor_get(v___x_2060_, 0);
v_nextMacroScope_2064_ = lean_ctor_get(v___x_2060_, 1);
v_ngen_2065_ = lean_ctor_get(v___x_2060_, 2);
v_auxDeclNGen_2066_ = lean_ctor_get(v___x_2060_, 3);
v_traceState_2067_ = lean_ctor_get(v___x_2060_, 4);
v_cache_2068_ = lean_ctor_get(v___x_2060_, 5);
v_messages_2069_ = lean_ctor_get(v___x_2060_, 6);
v_infoState_2070_ = lean_ctor_get(v___x_2060_, 7);
v_snapshotTasks_2071_ = lean_ctor_get(v___x_2060_, 8);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2073_ = v___x_2060_;
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snapshotTasks_2071_);
lean_inc(v_infoState_2070_);
lean_inc(v_messages_2069_);
lean_inc(v_cache_2068_);
lean_inc(v_traceState_2067_);
lean_inc(v_auxDeclNGen_2066_);
lean_inc(v_ngen_2065_);
lean_inc(v_nextMacroScope_2064_);
lean_inc(v_env_2063_);
lean_dec(v___x_2060_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_inc(v_openDecls_2062_);
lean_inc(v_currNamespace_2061_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_currNamespace_2061_);
lean_ctor_set(v___x_2075_, 1, v_openDecls_2062_);
v___x_2076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___y_2053_);
lean_inc_ref(v___y_2057_);
lean_inc_ref(v___y_2051_);
v___x_2077_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2077_, 0, v___y_2051_);
lean_ctor_set(v___x_2077_, 1, v___y_2056_);
lean_ctor_set(v___x_2077_, 2, v___y_2052_);
lean_ctor_set(v___x_2077_, 3, v___y_2057_);
lean_ctor_set(v___x_2077_, 4, v___x_2076_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5, v___y_2054_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5 + 1, v___y_2055_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5 + 2, v_isSilent_2044_);
v___x_2078_ = l_Lean_MessageLog_add(v___x_2077_, v_messages_2069_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 6, v___x_2078_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_env_2063_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_nextMacroScope_2064_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_ngen_2065_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_auxDeclNGen_2066_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_traceState_2067_);
lean_ctor_set(v_reuseFailAlloc_2084_, 5, v_cache_2068_);
lean_ctor_set(v_reuseFailAlloc_2084_, 6, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2084_, 7, v_infoState_2070_);
lean_ctor_set(v_reuseFailAlloc_2084_, 8, v_snapshotTasks_2071_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_st_ref_set(v___y_2059_, v___x_2080_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
v___jp_2086_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2110_; 
v___x_2095_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2042_);
v___x_2096_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_2095_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_inc_ref_n(v___y_2089_, 2);
v___x_2101_ = l_Lean_FileMap_toPosition(v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
v___x_2102_ = l_Lean_FileMap_toPosition(v___y_2089_, v___y_2094_);
lean_dec(v___y_2094_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
v___x_2104_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
if (v___y_2093_ == 0)
{
lean_del_object(v___x_2099_);
lean_dec_ref(v___y_2087_);
v___y_2051_ = v___y_2088_;
v___y_2052_ = v___x_2103_;
v___y_2053_ = v_a_2097_;
v___y_2054_ = v___y_2091_;
v___y_2055_ = v___y_2092_;
v___y_2056_ = v___x_2101_;
v___y_2057_ = v___x_2104_;
v___y_2058_ = v___y_2047_;
v___y_2059_ = v___y_2048_;
goto v___jp_2050_;
}
else
{
uint8_t v___x_2105_; 
lean_inc(v_a_2097_);
v___x_2105_ = l_Lean_MessageData_hasTag(v___y_2087_, v_a_2097_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec_ref(v___x_2103_);
lean_dec_ref(v___x_2101_);
lean_dec(v_a_2097_);
v___x_2106_ = lean_box(0);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2106_);
v___x_2108_ = v___x_2099_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
else
{
lean_del_object(v___x_2099_);
v___y_2051_ = v___y_2088_;
v___y_2052_ = v___x_2103_;
v___y_2053_ = v_a_2097_;
v___y_2054_ = v___y_2091_;
v___y_2055_ = v___y_2092_;
v___y_2056_ = v___x_2101_;
v___y_2057_ = v___x_2104_;
v___y_2058_ = v___y_2047_;
v___y_2059_ = v___y_2048_;
goto v___jp_2050_;
}
}
}
}
v___jp_2111_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Syntax_getTailPos_x3f(v___y_2115_, v___y_2116_);
lean_dec(v___y_2115_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_inc(v___y_2119_);
v___y_2087_ = v___y_2112_;
v___y_2088_ = v___y_2114_;
v___y_2089_ = v___y_2113_;
v___y_2090_ = v___y_2119_;
v___y_2091_ = v___y_2116_;
v___y_2092_ = v___y_2117_;
v___y_2093_ = v___y_2118_;
v___y_2094_ = v___y_2119_;
goto v___jp_2086_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2121_);
lean_dec_ref(v___x_2120_);
v___y_2087_ = v___y_2112_;
v___y_2088_ = v___y_2114_;
v___y_2089_ = v___y_2113_;
v___y_2090_ = v___y_2119_;
v___y_2091_ = v___y_2116_;
v___y_2092_ = v___y_2117_;
v___y_2093_ = v___y_2118_;
v___y_2094_ = v_val_2121_;
goto v___jp_2086_;
}
}
v___jp_2122_:
{
lean_object* v_ref_2130_; lean_object* v___x_2131_; 
v_ref_2130_ = l_Lean_replaceRef(v_ref_2041_, v___y_2126_);
v___x_2131_ = l_Lean_Syntax_getPos_x3f(v_ref_2130_, v___y_2127_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___y_2112_ = v___y_2123_;
v___y_2113_ = v___y_2125_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v_ref_2130_;
v___y_2116_ = v___y_2127_;
v___y_2117_ = v___y_2129_;
v___y_2118_ = v___y_2128_;
v___y_2119_ = v___x_2132_;
goto v___jp_2111_;
}
else
{
lean_object* v_val_2133_; 
v_val_2133_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v___x_2131_);
v___y_2112_ = v___y_2123_;
v___y_2113_ = v___y_2125_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v_ref_2130_;
v___y_2116_ = v___y_2127_;
v___y_2117_ = v___y_2129_;
v___y_2118_ = v___y_2128_;
v___y_2119_ = v_val_2133_;
goto v___jp_2111_;
}
}
v___jp_2135_:
{
if (v___y_2142_ == 0)
{
v___y_2123_ = v___y_2138_;
v___y_2124_ = v___y_2137_;
v___y_2125_ = v___y_2136_;
v___y_2126_ = v___y_2139_;
v___y_2127_ = v___y_2141_;
v___y_2128_ = v___y_2140_;
v___y_2129_ = v_severity_2043_;
goto v___jp_2122_;
}
else
{
v___y_2123_ = v___y_2138_;
v___y_2124_ = v___y_2137_;
v___y_2125_ = v___y_2136_;
v___y_2126_ = v___y_2139_;
v___y_2127_ = v___y_2141_;
v___y_2128_ = v___y_2140_;
v___y_2129_ = v___x_2134_;
goto v___jp_2122_;
}
}
v___jp_2143_:
{
if (v___y_2144_ == 0)
{
lean_object* v_fileName_2145_; lean_object* v_fileMap_2146_; lean_object* v_options_2147_; lean_object* v_ref_2148_; uint8_t v_suppressElabErrors_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; uint8_t v___x_2153_; uint8_t v___x_2154_; 
v_fileName_2145_ = lean_ctor_get(v___y_2047_, 0);
v_fileMap_2146_ = lean_ctor_get(v___y_2047_, 1);
v_options_2147_ = lean_ctor_get(v___y_2047_, 2);
v_ref_2148_ = lean_ctor_get(v___y_2047_, 5);
v_suppressElabErrors_2149_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*14 + 1);
v___x_2150_ = lean_box(v___y_2144_);
v___x_2151_ = lean_box(v_suppressElabErrors_2149_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2152_, 0, v___x_2150_);
lean_closure_set(v___f_2152_, 1, v___x_2151_);
v___x_2153_ = 1;
v___x_2154_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2043_, v___x_2153_);
if (v___x_2154_ == 0)
{
v___y_2136_ = v_fileMap_2146_;
v___y_2137_ = v_fileName_2145_;
v___y_2138_ = v___f_2152_;
v___y_2139_ = v_ref_2148_;
v___y_2140_ = v_suppressElabErrors_2149_;
v___y_2141_ = v___y_2144_;
v___y_2142_ = v___x_2154_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = l_Lean_warningAsError;
v___x_2156_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_2147_, v___x_2155_);
v___y_2136_ = v_fileMap_2146_;
v___y_2137_ = v_fileName_2145_;
v___y_2138_ = v___f_2152_;
v___y_2139_ = v_ref_2148_;
v___y_2140_ = v_suppressElabErrors_2149_;
v___y_2141_ = v___y_2144_;
v___y_2142_ = v___x_2156_;
goto v___jp_2135_;
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v_msgData_2042_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(lean_object* v_ref_2161_, lean_object* v_msgData_2162_, lean_object* v_severity_2163_, lean_object* v_isSilent_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v_severity_boxed_2170_; uint8_t v_isSilent_boxed_2171_; lean_object* v_res_2172_; 
v_severity_boxed_2170_ = lean_unbox(v_severity_2163_);
v_isSilent_boxed_2171_ = lean_unbox(v_isSilent_2164_);
v_res_2172_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2161_, v_msgData_2162_, v_severity_boxed_2170_, v_isSilent_boxed_2171_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_ref_2161_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object* v_ref_2173_, lean_object* v_msgData_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = 2;
v___x_2183_ = 0;
v___x_2184_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2173_, v_msgData_2174_, v___x_2182_, v___x_2183_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object* v_ref_2185_, lean_object* v_msgData_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v_ref_2185_, v_msgData_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v_ref_2185_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object* v_ref_2195_, lean_object* v_msgData_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = 1;
v___x_2205_ = 0;
v___x_2206_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2195_, v_msgData_2196_, v___x_2204_, v___x_2205_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object* v_ref_2207_, lean_object* v_msgData_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v_ref_2207_, v_msgData_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v_ref_2207_);
return v_res_2216_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* v_stx_2244_, lean_object* v_expType_x3f_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
uint8_t v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2274_; lean_object* v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v_fst_2346_; lean_object* v_snd_2347_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; uint8_t v___y_2375_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_inc(v_stx_2244_);
v___x_2393_ = l_Lean_Syntax_getKind(v_stx_2244_);
v___x_2394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_2392_, v___x_2393_);
lean_dec(v___x_2393_);
if (lean_obj_tag(v___x_2394_) == 1)
{
lean_object* v_val_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2428_; 
v_val_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_val_2395_);
lean_dec_ref(v___x_2394_);
v_fst_2396_ = lean_ctor_get(v_val_2395_, 0);
v_snd_2397_ = lean_ctor_get(v_val_2395_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_val_2395_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2399_ = v_val_2395_;
v_isShared_2400_ = v_isSharedCheck_2428_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v_val_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2428_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v_env_2402_; uint8_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2401_ = lean_st_ref_get(v_a_2251_);
v_env_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc_ref(v_env_2402_);
lean_dec(v___x_2401_);
v___x_2403_ = 1;
lean_inc(v_snd_2397_);
v___x_2404_ = l_Lean_Environment_contains(v_env_2402_, v_snd_2397_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_dec(v_expType_x3f_2245_);
lean_dec(v_stx_2244_);
v___x_2405_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
v___x_2406_ = l_Lean_MessageData_ofName(v_snd_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set_tag(v___x_2399_, 7);
lean_ctor_set(v___x_2399_, 1, v___x_2406_);
lean_ctor_set(v___x_2399_, 0, v___x_2405_);
v___x_2408_ = v___x_2399_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v___x_2409_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
v___x_2412_ = l_Lean_MessageData_ofName(v_fst_2396_);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = l_Lean_MessageData_hint_x27(v___x_2415_);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2410_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_2417_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_del_object(v___x_2399_);
lean_dec(v_snd_2397_);
lean_dec(v_fst_2396_);
v___y_2382_ = v_a_2246_;
v___y_2383_ = v_a_2247_;
v___y_2384_ = v_a_2248_;
v___y_2385_ = v_a_2249_;
v___y_2386_ = v_a_2250_;
v___y_2387_ = v_a_2251_;
goto v___jp_2381_;
}
}
}
else
{
lean_dec(v___x_2394_);
v___y_2382_ = v_a_2246_;
v___y_2383_ = v_a_2247_;
v___y_2384_ = v_a_2248_;
v___y_2385_ = v_a_2249_;
v___y_2386_ = v_a_2250_;
v___y_2387_ = v_a_2251_;
goto v___jp_2381_;
}
v___jp_2253_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed), 3, 1);
lean_closure_set(v___x_2261_, 0, v_stx_2244_);
v___x_2262_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_2261_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = l_Lean_Elab_Term_elabTerm(v_a_2263_, v_expType_x3f_2245_, v___y_2254_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2264_;
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_expType_x3f_2245_);
v_a_2265_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2262_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2262_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
v___jp_2273_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v_partialId_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2337_; 
v___x_2283_ = l_Lean_Syntax_getNumArgs(v___y_2282_);
v___x_2284_ = lean_unsigned_to_nat(2u);
v___x_2285_ = lean_nat_sub(v___x_2283_, v___x_2284_);
lean_dec(v___x_2283_);
v_partialId_2286_ = l_Lean_Syntax_getArg(v___y_2282_, v___x_2285_);
lean_dec(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___y_2282_);
lean_ctor_set(v___x_2287_, 1, v_partialId_2286_);
v___x_2288_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_2287_, v___y_2278_, v___y_2274_, v___y_2279_, v___y_2281_, v___y_2275_, v___y_2277_);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2288_, 0);
lean_dec(v_unused_2338_);
v___x_2290_ = v___x_2288_;
v_isShared_2291_ = v_isSharedCheck_2337_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v___x_2288_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2337_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2292_ = l_Lean_Syntax_getId(v___y_2280_);
v___x_2293_ = lean_erase_macro_scopes(v___x_2292_);
lean_inc(v___x_2293_);
lean_inc(v___y_2280_);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___y_2280_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 6);
lean_ctor_set(v___x_2290_, 0, v___x_2294_);
v___x_2296_ = v___x_2290_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_a_2299_; 
v___x_2297_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2296_, v___y_2278_, v___y_2274_, v___y_2279_, v___y_2281_, v___y_2275_, v___y_2277_);
lean_dec_ref(v___x_2297_);
v___x_2298_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_2293_, v___y_2277_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
if (lean_obj_tag(v_a_2299_) == 1)
{
lean_object* v_val_2300_; lean_object* v_metadata_2301_; lean_object* v_removedVersion_x3f_2302_; 
v_val_2300_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_val_2300_);
lean_dec_ref(v_a_2299_);
v_metadata_2301_ = lean_ctor_get(v_val_2300_, 1);
lean_inc_ref(v_metadata_2301_);
lean_dec(v_val_2300_);
v_removedVersion_x3f_2302_ = lean_ctor_get(v_metadata_2301_, 2);
lean_inc(v_removedVersion_x3f_2302_);
lean_dec_ref(v_metadata_2301_);
if (lean_obj_tag(v_removedVersion_x3f_2302_) == 1)
{
lean_object* v_val_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_val_2303_ = lean_ctor_get(v_removedVersion_x3f_2302_, 0);
lean_inc(v_val_2303_);
lean_dec_ref(v_removedVersion_x3f_2302_);
v___x_2304_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
v___x_2305_ = l_Lean_MessageData_ofName(v___x_2293_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = l_Lean_stringToMessageData(v_val_2303_);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_2280_, v___x_2312_, v___y_2278_, v___y_2274_, v___y_2279_, v___y_2281_, v___y_2275_, v___y_2277_);
lean_dec(v___y_2280_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref(v___x_2313_);
v___y_2254_ = v___y_2276_;
v___y_2255_ = v___y_2278_;
v___y_2256_ = v___y_2274_;
v___y_2257_ = v___y_2279_;
v___y_2258_ = v___y_2281_;
v___y_2259_ = v___y_2275_;
v___y_2260_ = v___y_2277_;
goto v___jp_2253_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_expType_x3f_2245_);
lean_dec(v_stx_2244_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_dec(v_removedVersion_x3f_2302_);
lean_dec(v___x_2293_);
lean_dec(v___y_2280_);
v___y_2254_ = v___y_2276_;
v___y_2255_ = v___y_2278_;
v___y_2256_ = v___y_2274_;
v___y_2257_ = v___y_2279_;
v___y_2258_ = v___y_2281_;
v___y_2259_ = v___y_2275_;
v___y_2260_ = v___y_2277_;
goto v___jp_2253_;
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v_a_2299_);
v___x_2322_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
v___x_2323_ = l_Lean_MessageData_ofName(v___x_2293_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_2280_, v___x_2326_, v___y_2278_, v___y_2274_, v___y_2279_, v___y_2281_, v___y_2275_, v___y_2277_);
lean_dec(v___y_2280_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_dec_ref(v___x_2327_);
v___y_2254_ = v___y_2276_;
v___y_2255_ = v___y_2278_;
v___y_2256_ = v___y_2274_;
v___y_2257_ = v___y_2279_;
v___y_2258_ = v___y_2281_;
v___y_2259_ = v___y_2275_;
v___y_2260_ = v___y_2277_;
goto v___jp_2253_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_expType_x3f_2245_);
lean_dec(v_stx_2244_);
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
}
v___jp_2339_:
{
lean_object* v___x_2348_; uint8_t v___x_2349_; uint8_t v___x_2350_; 
v___x_2348_ = l_Lean_Syntax_getNumArgs(v_stx_2244_);
v___x_2349_ = lean_nat_dec_eq(v___x_2348_, v_snd_2347_);
v___x_2350_ = 1;
if (v___x_2349_ == 0)
{
lean_dec(v___x_2348_);
lean_inc(v_stx_2244_);
v___y_2274_ = v___y_2340_;
v___y_2275_ = v___y_2341_;
v___y_2276_ = v___x_2350_;
v___y_2277_ = v___y_2343_;
v___y_2278_ = v___y_2342_;
v___y_2279_ = v___y_2344_;
v___y_2280_ = v_fst_2346_;
v___y_2281_ = v___y_2345_;
v___y_2282_ = v_stx_2244_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2351_ = l_Lean_Syntax_getArgs(v_stx_2244_);
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_sub(v___x_2348_, v___x_2352_);
lean_dec(v___x_2348_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = l_Array_toSubarray___redArg(v___x_2351_, v___x_2354_, v___x_2353_);
v___x_2356_ = l_Subarray_copy___redArg(v___x_2355_);
lean_inc(v_stx_2244_);
v___x_2357_ = l_Lean_Syntax_setArgs(v_stx_2244_, v___x_2356_);
v___y_2274_ = v___y_2340_;
v___y_2275_ = v___y_2341_;
v___y_2276_ = v___x_2350_;
v___y_2277_ = v___y_2343_;
v___y_2278_ = v___y_2342_;
v___y_2279_ = v___y_2344_;
v___y_2280_ = v_fst_2346_;
v___y_2281_ = v___y_2345_;
v___y_2282_ = v___x_2357_;
goto v___jp_2273_;
}
}
v___jp_2358_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_unsigned_to_nat(2u);
v___x_2366_ = l_Lean_Syntax_getArg(v_stx_2244_, v___x_2365_);
v___x_2367_ = lean_unsigned_to_nat(5u);
v___y_2340_ = v___y_2359_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___y_2362_;
v___y_2343_ = v___y_2361_;
v___y_2344_ = v___y_2363_;
v___y_2345_ = v___y_2364_;
v_fst_2346_ = v___x_2366_;
v_snd_2347_ = v___x_2367_;
goto v___jp_2339_;
}
v___jp_2368_:
{
if (v___y_2375_ == 0)
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_stx_2244_);
v___x_2377_ = l_Lean_Syntax_isOfKind(v_stx_2244_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = l_Lean_Syntax_getArg(v_stx_2244_, v___x_2378_);
v___x_2380_ = lean_unsigned_to_nat(4u);
v___y_2340_ = v___y_2369_;
v___y_2341_ = v___y_2370_;
v___y_2342_ = v___y_2372_;
v___y_2343_ = v___y_2371_;
v___y_2344_ = v___y_2373_;
v___y_2345_ = v___y_2374_;
v_fst_2346_ = v___x_2379_;
v_snd_2347_ = v___x_2380_;
goto v___jp_2339_;
}
else
{
v___y_2359_ = v___y_2369_;
v___y_2360_ = v___y_2370_;
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2372_;
v___y_2363_ = v___y_2373_;
v___y_2364_ = v___y_2374_;
goto v___jp_2358_;
}
}
else
{
v___y_2359_ = v___y_2369_;
v___y_2360_ = v___y_2370_;
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2372_;
v___y_2363_ = v___y_2373_;
v___y_2364_ = v___y_2374_;
goto v___jp_2358_;
}
}
v___jp_2381_:
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_stx_2244_);
v___x_2389_ = l_Lean_Syntax_isOfKind(v_stx_2244_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_stx_2244_);
v___x_2391_ = l_Lean_Syntax_isOfKind(v_stx_2244_, v___x_2390_);
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2387_;
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2384_;
v___y_2374_ = v___y_2385_;
v___y_2375_ = v___x_2391_;
goto v___jp_2368_;
}
else
{
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2387_;
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2384_;
v___y_2374_ = v___y_2385_;
v___y_2375_ = v___x_2389_;
goto v___jp_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object* v_stx_2429_, lean_object* v_expType_x3f_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(v_stx_2429_, v_expType_x3f_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object* v_00_u03b1_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_2440_, v___y_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_x_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_2444_, v_x_2445_, v___y_2446_, v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec_ref(v_x_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object* v_00_u03b1_2449_, lean_object* v_ref_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_2450_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_ref_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_2459_, v_ref_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object* v_00_u03b1_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* v_00_u03b1_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_x_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(v_00_u03b1_2497_, v_x_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(lean_object* v_t_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_2507_, v___y_2513_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(lean_object* v_t_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object* v_00_u03b2_2525_, lean_object* v_m_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_2526_, v_a_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object* v_00_u03b2_2529_, lean_object* v_m_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_2529_, v_m_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_m_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object* v_00_u03b1_2533_, lean_object* v_msg_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object* v_00_u03b1_2543_, lean_object* v_msg_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(v_00_u03b1_2543_, v_msg_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object* v_cls_2553_, lean_object* v_msg_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_2553_, v_msg_2554_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object* v_cls_2563_, lean_object* v_msg_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_2563_, v_msg_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object* v_as_2573_, lean_object* v_as_x27_2574_, lean_object* v_b_2575_, lean_object* v_a_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_2574_, v_b_2575_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object* v_as_2585_, lean_object* v_as_x27_2586_, lean_object* v_b_2587_, lean_object* v_a_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_2585_, v_as_x27_2586_, v_b_2587_, v_a_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v_as_x27_2586_);
lean_dec(v_as_2585_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object* v_00_u03b1_2597_, lean_object* v_ref_2598_, lean_object* v_msg_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_2598_, v_msg_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_ref_2609_, lean_object* v_msg_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_2608_, v_ref_2609_, v_msg_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v_ref_2609_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(lean_object* v_ref_2619_, lean_object* v_msgData_2620_, uint8_t v_severity_2621_, uint8_t v_isSilent_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2619_, v_msgData_2620_, v_severity_2621_, v_isSilent_2622_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(lean_object* v_ref_2631_, lean_object* v_msgData_2632_, lean_object* v_severity_2633_, lean_object* v_isSilent_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v_severity_boxed_2642_; uint8_t v_isSilent_boxed_2643_; lean_object* v_res_2644_; 
v_severity_boxed_2642_ = lean_unbox(v_severity_2633_);
v_isSilent_boxed_2643_ = lean_unbox(v_isSilent_2634_);
v_res_2644_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_2631_, v_msgData_2632_, v_severity_boxed_2642_, v_isSilent_boxed_2643_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v_ref_2631_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(lean_object* v_00_u03b2_2645_, lean_object* v_a_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_2646_, v_x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(lean_object* v_00_u03b2_2649_, lean_object* v_a_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_2649_, v_a_2650_, v_x_2651_);
lean_dec(v_x_2651_);
lean_dec(v_a_2650_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object* v_msgData_2653_, lean_object* v_macroStack_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_2653_, v_macroStack_2654_, v___y_2659_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object* v_msgData_2663_, lean_object* v_macroStack_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_2663_, v_macroStack_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(lean_object* v_00_u03b2_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_2674_, v_x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(lean_object* v_00_u03b2_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_2677_, v_x_2678_, v_x_2679_);
lean_dec_ref(v_x_2679_);
lean_dec_ref(v_x_2678_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(lean_object* v_00_u03b2_2682_, lean_object* v_x_2683_, size_t v_x_2684_, lean_object* v_x_2685_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_2683_, v_x_2684_, v_x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(lean_object* v_00_u03b2_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
size_t v_x_22597__boxed_2691_; uint8_t v_res_2692_; lean_object* v_r_2693_; 
v_x_22597__boxed_2691_ = lean_unbox_usize(v_x_2689_);
lean_dec(v_x_2689_);
v_res_2692_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_2687_, v_x_2688_, v_x_22597__boxed_2691_, v_x_2690_);
lean_dec_ref(v_x_2690_);
lean_dec_ref(v_x_2688_);
v_r_2693_ = lean_box(v_res_2692_);
return v_r_2693_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(lean_object* v_00_u03b2_2694_, lean_object* v_keys_2695_, lean_object* v_vals_2696_, lean_object* v_heq_2697_, lean_object* v_i_2698_, lean_object* v_k_2699_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_2695_, v_i_2698_, v_k_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(lean_object* v_00_u03b2_2701_, lean_object* v_keys_2702_, lean_object* v_vals_2703_, lean_object* v_heq_2704_, lean_object* v_i_2705_, lean_object* v_k_2706_){
_start:
{
uint8_t v_res_2707_; lean_object* v_r_2708_; 
v_res_2707_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_2701_, v_keys_2702_, v_vals_2703_, v_heq_2704_, v_i_2705_, v_k_2706_);
lean_dec_ref(v_k_2706_);
lean_dec_ref(v_vals_2703_);
lean_dec_ref(v_keys_2702_);
v_r_2708_ = lean_box(v_res_2707_);
return v_r_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2717_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2718_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2720_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2721_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2717_, v___x_2718_, v___x_2719_, v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2725_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2726_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
v___x_2727_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2728_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2729_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2725_, v___x_2726_, v___x_2727_, v___x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2733_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2734_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
v___x_2735_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2736_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2737_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2733_, v___x_2734_, v___x_2735_, v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2741_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2742_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2744_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2745_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2741_, v___x_2742_, v___x_2743_, v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2749_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2750_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
v___x_2751_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2752_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2753_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2749_, v___x_2750_, v___x_2751_, v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2757_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2758_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2760_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2761_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2757_, v___x_2758_, v___x_2759_, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
return v_res_2763_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = lean_box(0);
v___x_2765_ = l_Lean_Elab_abortTermExceptionId;
v___x_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg(){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___boxed(lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(lean_object* v_00_u03b1_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(v_00_u03b1_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* v_t_2790_, lean_object* v_tp_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_inc_ref(v_tp_2791_);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v_tp_2791_);
v___x_2800_ = 1;
v___x_2801_ = lean_box(0);
v___x_2802_ = l_Lean_Elab_Term_elabTermEnsuringType(v_t_2790_, v___x_2799_, v___x_2800_, v___x_2800_, v___x_2801_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___x_2811_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref(v___x_2802_);
v___x_2811_ = l_Lean_Expr_hasSyntheticSorry(v_a_2803_);
if (v___x_2811_ == 0)
{
v___y_2805_ = v_a_2794_;
v___y_2806_ = v_a_2795_;
v___y_2807_ = v_a_2796_;
v___y_2808_ = v_a_2797_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_dec_ref(v___x_2812_);
v___y_2805_ = v_a_2794_;
v___y_2806_ = v_a_2795_;
v___y_2807_ = v_a_2796_;
v___y_2808_ = v_a_2797_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_a_2803_);
lean_dec_ref(v_tp_2791_);
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
}
v___jp_2804_:
{
uint8_t v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = 1;
v___x_2810_ = l_Lean_Meta_evalExpr___redArg(v_tp_2791_, v_a_2803_, v___x_2809_, v___x_2800_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2810_;
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref(v_tp_2791_);
v_a_2821_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2802_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2802_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object* v_t_2829_, lean_object* v_tp_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2829_, v_tp_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg(){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* v_00_u03b1_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* v_00_u03b1_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v_env_2857_; lean_object* v___x_2858_; lean_object* v_mainModule_2859_; lean_object* v___x_2860_; 
v___x_2856_ = lean_st_ref_get(v___y_2854_);
v_env_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc_ref(v_env_2857_);
lean_dec(v___x_2856_);
v___x_2858_ = l_Lean_Environment_header(v_env_2857_);
lean_dec_ref(v_env_2857_);
v_mainModule_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_mainModule_2859_);
lean_dec_ref(v___x_2858_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_mainModule_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_2861_);
lean_dec(v___y_2861_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* v_t_2872_, lean_object* v___x_2873_, lean_object* v_x_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2872_, v___x_2873_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object* v_t_2883_, lean_object* v___x_2884_, lean_object* v_x_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(v_t_2883_, v___x_2884_, v_x_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v_x_2885_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(lean_object* v_msgData_2894_, lean_object* v_macroStack_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_scopes_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v_opts_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2898_ = lean_st_ref_get(v___y_2896_);
v_scopes_2899_ = lean_ctor_get(v___x_2898_, 2);
lean_inc(v_scopes_2899_);
lean_dec(v___x_2898_);
v___x_2900_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2901_ = l_List_head_x21___redArg(v___x_2900_, v_scopes_2899_);
lean_dec(v_scopes_2899_);
v_opts_2902_ = lean_ctor_get(v___x_2901_, 1);
lean_inc_ref(v_opts_2902_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_Elab_pp_macroStack;
v___x_2904_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_2902_, v___x_2903_);
lean_dec_ref(v_opts_2902_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_macroStack_2895_);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_msgData_2894_);
return v___x_2905_;
}
else
{
if (lean_obj_tag(v_macroStack_2895_) == 0)
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_msgData_2894_);
return v___x_2906_;
}
else
{
lean_object* v_head_2907_; lean_object* v_after_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2923_; 
v_head_2907_ = lean_ctor_get(v_macroStack_2895_, 0);
lean_inc(v_head_2907_);
v_after_2908_ = lean_ctor_get(v_head_2907_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_head_2907_);
if (v_isSharedCheck_2923_ == 0)
{
lean_object* v_unused_2924_; 
v_unused_2924_ = lean_ctor_get(v_head_2907_, 0);
lean_dec(v_unused_2924_);
v___x_2910_ = v_head_2907_;
v_isShared_2911_ = v_isSharedCheck_2923_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_after_2908_);
lean_dec(v_head_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2923_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_2911_ == 0)
{
lean_ctor_set_tag(v___x_2910_, 7);
lean_ctor_set(v___x_2910_, 1, v___x_2912_);
lean_ctor_set(v___x_2910_, 0, v_msgData_2894_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_msgData_2894_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_msgData_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2915_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = l_Lean_MessageData_ofSyntax(v_after_2908_);
v___x_2918_ = l_Lean_indentD(v___x_2917_);
v_msgData_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2919_, 0, v___x_2916_);
lean_ctor_set(v_msgData_2919_, 1, v___x_2918_);
v___x_2920_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_2919_, v_macroStack_2895_);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_2925_, lean_object* v_macroStack_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_2925_, v_macroStack_2926_, v___y_2927_);
lean_dec(v___y_2927_);
return v_res_2929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
lean_ctor_set(v___x_2935_, 2, v___x_2934_);
lean_ctor_set(v___x_2935_, 3, v___x_2934_);
lean_ctor_set(v___x_2935_, 4, v___x_2933_);
lean_ctor_set(v___x_2935_, 5, v___x_2933_);
lean_ctor_set(v___x_2935_, 6, v___x_2933_);
lean_ctor_set(v___x_2935_, 7, v___x_2933_);
lean_ctor_set(v___x_2935_, 8, v___x_2933_);
lean_ctor_set(v___x_2935_, 9, v___x_2933_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(32u);
v___x_2937_ = lean_mk_empty_array_with_capacity(v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2939_ = ((size_t)5ULL);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_unsigned_to_nat(32u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
v___x_2943_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3);
v___x_2944_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_ctor_set(v___x_2944_, 1, v___x_2942_);
lean_ctor_set(v___x_2944_, 2, v___x_2940_);
lean_ctor_set(v___x_2944_, 3, v___x_2940_);
lean_ctor_set_usize(v___x_2944_, 4, v___x_2939_);
return v___x_2944_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2945_ = lean_box(1);
v___x_2946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4);
v___x_2947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
v___x_2948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
lean_ctor_set(v___x_2948_, 2, v___x_2945_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(lean_object* v_msgData_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; lean_object* v_env_2953_; lean_object* v___x_2954_; lean_object* v_scopes_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v_opts_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2952_ = lean_st_ref_get(v___y_2950_);
v_env_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc_ref(v_env_2953_);
lean_dec(v___x_2952_);
v___x_2954_ = lean_st_ref_get(v___y_2950_);
v_scopes_2955_ = lean_ctor_get(v___x_2954_, 2);
lean_inc(v_scopes_2955_);
lean_dec(v___x_2954_);
v___x_2956_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2957_ = l_List_head_x21___redArg(v___x_2956_, v_scopes_2955_);
lean_dec(v_scopes_2955_);
v_opts_2958_ = lean_ctor_get(v___x_2957_, 1);
lean_inc_ref(v_opts_2958_);
lean_dec(v___x_2957_);
v___x_2959_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2);
v___x_2960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5);
v___x_2961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2961_, 0, v_env_2953_);
lean_ctor_set(v___x_2961_, 1, v___x_2959_);
lean_ctor_set(v___x_2961_, 2, v___x_2960_);
lean_ctor_set(v___x_2961_, 3, v_opts_2958_);
v___x_2962_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_msgData_2949_);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_2964_, v___y_2965_);
lean_dec(v___y_2965_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object* v_msg_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Elab_Command_getRef___redArg(v___y_2969_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v_macroStack_2974_; lean_object* v___x_2975_; lean_object* v_a_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2987_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2972_);
v_macroStack_2974_ = lean_ctor_get(v___y_2969_, 4);
v___x_2975_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_2968_, v___y_2970_);
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = l_Lean_Elab_getBetterRef(v_a_2973_, v_macroStack_2974_);
lean_dec(v_a_2973_);
lean_inc(v_macroStack_2974_);
v___x_2978_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_a_2976_, v_macroStack_2974_, v___y_2970_);
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2977_);
lean_ctor_set(v___x_2983_, 1, v_a_2979_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 1);
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_msg_2968_);
v_a_2988_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2972_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2972_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object* v_msg_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object* v_ref_3001_, lean_object* v_msg_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Elab_Command_getRef___redArg(v___y_3003_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_fileName_3008_; lean_object* v_fileMap_3009_; lean_object* v_currRecDepth_3010_; lean_object* v_cmdPos_3011_; lean_object* v_macroStack_3012_; lean_object* v_quotContext_x3f_3013_; lean_object* v_currMacroScope_3014_; lean_object* v_snap_x3f_3015_; lean_object* v_cancelTk_x3f_3016_; uint8_t v_suppressElabErrors_3017_; lean_object* v_ref_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v_fileName_3008_ = lean_ctor_get(v___y_3003_, 0);
v_fileMap_3009_ = lean_ctor_get(v___y_3003_, 1);
v_currRecDepth_3010_ = lean_ctor_get(v___y_3003_, 2);
v_cmdPos_3011_ = lean_ctor_get(v___y_3003_, 3);
v_macroStack_3012_ = lean_ctor_get(v___y_3003_, 4);
v_quotContext_x3f_3013_ = lean_ctor_get(v___y_3003_, 5);
v_currMacroScope_3014_ = lean_ctor_get(v___y_3003_, 6);
v_snap_x3f_3015_ = lean_ctor_get(v___y_3003_, 8);
v_cancelTk_x3f_3016_ = lean_ctor_get(v___y_3003_, 9);
v_suppressElabErrors_3017_ = lean_ctor_get_uint8(v___y_3003_, sizeof(void*)*10);
v_ref_3018_ = l_Lean_replaceRef(v_ref_3001_, v_a_3007_);
lean_dec(v_a_3007_);
lean_inc(v_cancelTk_x3f_3016_);
lean_inc(v_snap_x3f_3015_);
lean_inc(v_currMacroScope_3014_);
lean_inc(v_quotContext_x3f_3013_);
lean_inc(v_macroStack_3012_);
lean_inc(v_cmdPos_3011_);
lean_inc(v_currRecDepth_3010_);
lean_inc_ref(v_fileMap_3009_);
lean_inc_ref(v_fileName_3008_);
v___x_3019_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3019_, 0, v_fileName_3008_);
lean_ctor_set(v___x_3019_, 1, v_fileMap_3009_);
lean_ctor_set(v___x_3019_, 2, v_currRecDepth_3010_);
lean_ctor_set(v___x_3019_, 3, v_cmdPos_3011_);
lean_ctor_set(v___x_3019_, 4, v_macroStack_3012_);
lean_ctor_set(v___x_3019_, 5, v_quotContext_x3f_3013_);
lean_ctor_set(v___x_3019_, 6, v_currMacroScope_3014_);
lean_ctor_set(v___x_3019_, 7, v_ref_3018_);
lean_ctor_set(v___x_3019_, 8, v_snap_x3f_3015_);
lean_ctor_set(v___x_3019_, 9, v_cancelTk_x3f_3016_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*10, v_suppressElabErrors_3017_);
v___x_3020_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_3002_, v___x_3019_, v___y_3004_);
lean_dec_ref(v___x_3019_);
return v___x_3020_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v_msg_3002_);
v_a_3021_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3006_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3006_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object* v_ref_3029_, lean_object* v_msg_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_3029_, v_msg_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v_ref_3029_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(lean_object* v_cls_3035_, lean_object* v_msg_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Elab_Command_getRef___redArg(v___y_3037_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3089_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_3036_, v___y_3038_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3089_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3089_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v_traceState_3048_; lean_object* v_env_3049_; lean_object* v_messages_3050_; lean_object* v_scopes_3051_; lean_object* v_usedQuotCtxts_3052_; lean_object* v_nextMacroScope_3053_; lean_object* v_maxRecDepth_3054_; lean_object* v_ngen_3055_; lean_object* v_auxDeclNGen_3056_; lean_object* v_infoState_3057_; lean_object* v_snapshotTasks_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3088_; 
v___x_3047_ = lean_st_ref_take(v___y_3038_);
v_traceState_3048_ = lean_ctor_get(v___x_3047_, 9);
v_env_3049_ = lean_ctor_get(v___x_3047_, 0);
v_messages_3050_ = lean_ctor_get(v___x_3047_, 1);
v_scopes_3051_ = lean_ctor_get(v___x_3047_, 2);
v_usedQuotCtxts_3052_ = lean_ctor_get(v___x_3047_, 3);
v_nextMacroScope_3053_ = lean_ctor_get(v___x_3047_, 4);
v_maxRecDepth_3054_ = lean_ctor_get(v___x_3047_, 5);
v_ngen_3055_ = lean_ctor_get(v___x_3047_, 6);
v_auxDeclNGen_3056_ = lean_ctor_get(v___x_3047_, 7);
v_infoState_3057_ = lean_ctor_get(v___x_3047_, 8);
v_snapshotTasks_3058_ = lean_ctor_get(v___x_3047_, 10);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3060_ = v___x_3047_;
v_isShared_3061_ = v_isSharedCheck_3088_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_snapshotTasks_3058_);
lean_inc(v_traceState_3048_);
lean_inc(v_infoState_3057_);
lean_inc(v_auxDeclNGen_3056_);
lean_inc(v_ngen_3055_);
lean_inc(v_maxRecDepth_3054_);
lean_inc(v_nextMacroScope_3053_);
lean_inc(v_usedQuotCtxts_3052_);
lean_inc(v_scopes_3051_);
lean_inc(v_messages_3050_);
lean_inc(v_env_3049_);
lean_dec(v___x_3047_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3088_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
uint64_t v_tid_3062_; lean_object* v_traces_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3087_; 
v_tid_3062_ = lean_ctor_get_uint64(v_traceState_3048_, sizeof(void*)*1);
v_traces_3063_ = lean_ctor_get(v_traceState_3048_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_traceState_3048_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3065_ = v_traceState_3048_;
v_isShared_3066_ = v_isSharedCheck_3087_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_traces_3063_);
lean_dec(v_traceState_3048_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3087_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; double v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_3069_ = 0;
v___x_3070_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3071_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3071_, 0, v_cls_3035_);
lean_ctor_set(v___x_3071_, 1, v___x_3067_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
lean_ctor_set_float(v___x_3071_, sizeof(void*)*3, v___x_3068_);
lean_ctor_set_float(v___x_3071_, sizeof(void*)*3 + 8, v___x_3068_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3 + 16, v___x_3069_);
v___x_3072_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_3073_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set(v___x_3073_, 1, v_a_3043_);
lean_ctor_set(v___x_3073_, 2, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_a_3041_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = l_Lean_PersistentArray_push___redArg(v_traces_3063_, v___x_3074_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3075_);
v___x_3077_ = v___x_3065_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3075_);
lean_ctor_set_uint64(v_reuseFailAlloc_3086_, sizeof(void*)*1, v_tid_3062_);
v___x_3077_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3079_; 
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 9, v___x_3077_);
v___x_3079_ = v___x_3060_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_env_3049_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_messages_3050_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_scopes_3051_);
lean_ctor_set(v_reuseFailAlloc_3085_, 3, v_usedQuotCtxts_3052_);
lean_ctor_set(v_reuseFailAlloc_3085_, 4, v_nextMacroScope_3053_);
lean_ctor_set(v_reuseFailAlloc_3085_, 5, v_maxRecDepth_3054_);
lean_ctor_set(v_reuseFailAlloc_3085_, 6, v_ngen_3055_);
lean_ctor_set(v_reuseFailAlloc_3085_, 7, v_auxDeclNGen_3056_);
lean_ctor_set(v_reuseFailAlloc_3085_, 8, v_infoState_3057_);
lean_ctor_set(v_reuseFailAlloc_3085_, 9, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3085_, 10, v_snapshotTasks_3058_);
v___x_3079_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3080_ = lean_st_ref_set(v___y_3038_, v___x_3079_);
v___x_3081_ = lean_box(0);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3081_);
v___x_3083_ = v___x_3045_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec_ref(v_msg_3036_);
lean_dec(v_cls_3035_);
v_a_3090_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3040_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3040_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___boxed(lean_object* v_cls_3098_, lean_object* v_msg_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_3098_, v_msg_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(lean_object* v_mod_3104_, uint8_t v_isMeta_3105_, lean_object* v_hint_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; lean_object* v_env_3111_; uint8_t v_isExporting_3112_; lean_object* v___x_3113_; lean_object* v_env_3114_; lean_object* v___x_3115_; lean_object* v_entry_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___y_3121_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3110_ = lean_st_ref_get(v___y_3108_);
v_env_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc_ref(v_env_3111_);
lean_dec(v___x_3110_);
v_isExporting_3112_ = lean_ctor_get_uint8(v_env_3111_, sizeof(void*)*8);
lean_dec_ref(v_env_3111_);
v___x_3113_ = lean_st_ref_get(v___y_3108_);
v_env_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_ref(v_env_3114_);
lean_dec(v___x_3113_);
v___x_3115_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_3104_);
v_entry_3116_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3116_, 0, v_mod_3104_);
lean_ctor_set_uint8(v_entry_3116_, sizeof(void*)*1, v_isExporting_3112_);
lean_ctor_set_uint8(v_entry_3116_, sizeof(void*)*1 + 1, v_isMeta_3105_);
v___x_3117_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3118_ = lean_box(1);
v___x_3119_ = lean_box(0);
v___x_3147_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3115_, v___x_3117_, v_env_3114_, v___x_3118_, v___x_3119_);
v___x_3148_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_3147_, v_entry_3116_);
lean_dec(v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_scopes_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v_opts_3155_; uint8_t v_hasTrace_3156_; 
v___x_3149_ = l_Lean_inheritedTraceOptions;
v___x_3150_ = lean_st_ref_get(v___x_3149_);
v___x_3151_ = lean_st_ref_get(v___y_3108_);
v_scopes_3152_ = lean_ctor_get(v___x_3151_, 2);
lean_inc(v_scopes_3152_);
lean_dec(v___x_3151_);
v___x_3153_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3154_ = l_List_head_x21___redArg(v___x_3153_, v_scopes_3152_);
lean_dec(v_scopes_3152_);
v_opts_3155_ = lean_ctor_get(v___x_3154_, 1);
lean_inc_ref(v_opts_3155_);
lean_dec(v___x_3154_);
v_hasTrace_3156_ = lean_ctor_get_uint8(v_opts_3155_, sizeof(void*)*1);
if (v_hasTrace_3156_ == 0)
{
lean_dec_ref(v_opts_3155_);
lean_dec(v___x_3150_);
lean_dec(v_hint_3106_);
lean_dec(v_mod_3104_);
v___y_3121_ = v___y_3108_;
goto v___jp_3120_;
}
else
{
lean_object* v_cls_3157_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v_cls_3157_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_3177_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
v___x_3178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3150_, v_opts_3155_, v___x_3177_);
lean_dec_ref(v_opts_3155_);
lean_dec(v___x_3150_);
if (v___x_3178_ == 0)
{
lean_dec(v_hint_3106_);
lean_dec(v_mod_3104_);
v___y_3121_ = v___y_3108_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3179_; lean_object* v___y_3181_; 
v___x_3179_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_3112_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21));
v___y_3181_ = v___x_3188_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3189_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22));
v___y_3181_ = v___x_3189_;
goto v___jp_3180_;
}
v___jp_3180_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_inc_ref(v___y_3181_);
v___x_3182_ = l_Lean_stringToMessageData(v___y_3181_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3179_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
if (v_isMeta_3105_ == 0)
{
lean_object* v___x_3186_; 
v___x_3186_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_3164_ = v___x_3185_;
v___y_3165_ = v___x_3186_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3187_; 
v___x_3187_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_3164_ = v___x_3185_;
v___y_3165_ = v___x_3187_;
goto v___jp_3163_;
}
}
}
v___jp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___y_3159_);
lean_ctor_set(v___x_3161_, 1, v___y_3160_);
v___x_3162_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_3157_, v___x_3161_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_dec_ref(v___x_3162_);
v___y_3121_ = v___y_3108_;
goto v___jp_3120_;
}
else
{
lean_dec_ref(v_entry_3116_);
return v___x_3162_;
}
}
v___jp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
lean_inc_ref(v___y_3165_);
v___x_3166_ = l_Lean_stringToMessageData(v___y_3165_);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3164_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_Lean_MessageData_ofName(v_mod_3104_);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Lean_Name_isAnonymous(v_hint_3106_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_3174_ = l_Lean_MessageData_ofName(v_hint_3106_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___y_3159_ = v___x_3171_;
v___y_3160_ = v___x_3175_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3176_; 
lean_dec(v_hint_3106_);
v___x_3176_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
v___y_3159_ = v___x_3171_;
v___y_3160_ = v___x_3176_;
goto v___jp_3158_;
}
}
}
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec_ref(v_entry_3116_);
lean_dec(v_hint_3106_);
lean_dec(v_mod_3104_);
v___x_3190_ = lean_box(0);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
v___jp_3120_:
{
lean_object* v___x_3122_; lean_object* v_toEnvExtension_3123_; lean_object* v_env_3124_; lean_object* v_messages_3125_; lean_object* v_scopes_3126_; lean_object* v_usedQuotCtxts_3127_; lean_object* v_nextMacroScope_3128_; lean_object* v_maxRecDepth_3129_; lean_object* v_ngen_3130_; lean_object* v_auxDeclNGen_3131_; lean_object* v_infoState_3132_; lean_object* v_traceState_3133_; lean_object* v_snapshotTasks_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3146_; 
v___x_3122_ = lean_st_ref_take(v___y_3121_);
v_toEnvExtension_3123_ = lean_ctor_get(v___x_3117_, 0);
v_env_3124_ = lean_ctor_get(v___x_3122_, 0);
v_messages_3125_ = lean_ctor_get(v___x_3122_, 1);
v_scopes_3126_ = lean_ctor_get(v___x_3122_, 2);
v_usedQuotCtxts_3127_ = lean_ctor_get(v___x_3122_, 3);
v_nextMacroScope_3128_ = lean_ctor_get(v___x_3122_, 4);
v_maxRecDepth_3129_ = lean_ctor_get(v___x_3122_, 5);
v_ngen_3130_ = lean_ctor_get(v___x_3122_, 6);
v_auxDeclNGen_3131_ = lean_ctor_get(v___x_3122_, 7);
v_infoState_3132_ = lean_ctor_get(v___x_3122_, 8);
v_traceState_3133_ = lean_ctor_get(v___x_3122_, 9);
v_snapshotTasks_3134_ = lean_ctor_get(v___x_3122_, 10);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3136_ = v___x_3122_;
v_isShared_3137_ = v_isSharedCheck_3146_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_snapshotTasks_3134_);
lean_inc(v_traceState_3133_);
lean_inc(v_infoState_3132_);
lean_inc(v_auxDeclNGen_3131_);
lean_inc(v_ngen_3130_);
lean_inc(v_maxRecDepth_3129_);
lean_inc(v_nextMacroScope_3128_);
lean_inc(v_usedQuotCtxts_3127_);
lean_inc(v_scopes_3126_);
lean_inc(v_messages_3125_);
lean_inc(v_env_3124_);
lean_dec(v___x_3122_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3146_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_asyncMode_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v_asyncMode_3138_ = lean_ctor_get(v_toEnvExtension_3123_, 2);
v___x_3139_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3117_, v_env_3124_, v_entry_3116_, v_asyncMode_3138_, v___x_3119_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3139_);
v___x_3141_ = v___x_3136_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_messages_3125_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_scopes_3126_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_usedQuotCtxts_3127_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_nextMacroScope_3128_);
lean_ctor_set(v_reuseFailAlloc_3145_, 5, v_maxRecDepth_3129_);
lean_ctor_set(v_reuseFailAlloc_3145_, 6, v_ngen_3130_);
lean_ctor_set(v_reuseFailAlloc_3145_, 7, v_auxDeclNGen_3131_);
lean_ctor_set(v_reuseFailAlloc_3145_, 8, v_infoState_3132_);
lean_ctor_set(v_reuseFailAlloc_3145_, 9, v_traceState_3133_);
lean_ctor_set(v_reuseFailAlloc_3145_, 10, v_snapshotTasks_3134_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_st_ref_set(v___y_3121_, v___x_3141_);
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(lean_object* v_mod_3192_, lean_object* v_isMeta_3193_, lean_object* v_hint_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
uint8_t v_isMeta_boxed_3198_; lean_object* v_res_3199_; 
v_isMeta_boxed_3198_ = lean_unbox(v_isMeta_3193_);
v_res_3199_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_3192_, v_isMeta_boxed_3198_, v_hint_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(lean_object* v___x_3200_, lean_object* v_declName_3201_, lean_object* v_as_3202_, size_t v_sz_3203_, size_t v_i_3204_, lean_object* v_b_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_usize_dec_lt(v_i_3204_, v_sz_3203_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec(v_declName_3201_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_b_3205_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; lean_object* v_modules_3212_; lean_object* v___x_3213_; lean_object* v_a_3214_; lean_object* v___x_3215_; lean_object* v_toImport_3216_; lean_object* v_module_3217_; uint8_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3211_ = l_Lean_Environment_header(v___x_3200_);
v_modules_3212_ = lean_ctor_get(v___x_3211_, 3);
lean_inc_ref(v_modules_3212_);
lean_dec_ref(v___x_3211_);
v___x_3213_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3214_ = lean_array_uget_borrowed(v_as_3202_, v_i_3204_);
v___x_3215_ = lean_array_get(v___x_3213_, v_modules_3212_, v_a_3214_);
lean_dec_ref(v_modules_3212_);
v_toImport_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc_ref(v_toImport_3216_);
lean_dec(v___x_3215_);
v_module_3217_ = lean_ctor_get(v_toImport_3216_, 0);
lean_inc(v_module_3217_);
lean_dec_ref(v_toImport_3216_);
v___x_3218_ = 0;
lean_inc(v_declName_3201_);
v___x_3219_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3217_, v___x_3218_, v_declName_3201_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; 
lean_dec_ref(v___x_3219_);
v___x_3220_ = lean_box(0);
v___x_3221_ = ((size_t)1ULL);
v___x_3222_ = lean_usize_add(v_i_3204_, v___x_3221_);
v_i_3204_ = v___x_3222_;
v_b_3205_ = v___x_3220_;
goto _start;
}
else
{
lean_dec(v_declName_3201_);
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(lean_object* v___x_3224_, lean_object* v_declName_3225_, lean_object* v_as_3226_, lean_object* v_sz_3227_, lean_object* v_i_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
size_t v_sz_boxed_3233_; size_t v_i_boxed_3234_; lean_object* v_res_3235_; 
v_sz_boxed_3233_ = lean_unbox_usize(v_sz_3227_);
lean_dec(v_sz_3227_);
v_i_boxed_3234_ = lean_unbox_usize(v_i_3228_);
lean_dec(v_i_3228_);
v_res_3235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_3224_, v_declName_3225_, v_as_3226_, v_sz_boxed_3233_, v_i_boxed_3234_, v_b_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec_ref(v_as_3226_);
lean_dec_ref(v___x_3224_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(lean_object* v_declName_3236_, uint8_t v_isMeta_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; lean_object* v_env_3245_; lean_object* v___y_3247_; lean_object* v___x_3260_; 
v___x_3241_ = lean_st_ref_get(v___y_3239_);
v_env_3245_ = lean_ctor_get(v___x_3241_, 0);
lean_inc_ref(v_env_3245_);
lean_dec(v___x_3241_);
v___x_3260_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3245_, v_declName_3236_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_dec_ref(v_env_3245_);
lean_dec(v_declName_3236_);
goto v___jp_3242_;
}
else
{
lean_object* v_val_3261_; lean_object* v___x_3262_; lean_object* v_modules_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v_val_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_val_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = l_Lean_Environment_header(v_env_3245_);
v_modules_3263_ = lean_ctor_get(v___x_3262_, 3);
lean_inc_ref(v_modules_3263_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = lean_array_get_size(v_modules_3263_);
v___x_3265_ = lean_nat_dec_lt(v_val_3261_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_dec_ref(v_modules_3263_);
lean_dec(v_val_3261_);
lean_dec_ref(v_env_3245_);
lean_dec(v_declName_3236_);
goto v___jp_3242_;
}
else
{
lean_object* v___x_3266_; lean_object* v_env_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___y_3271_; 
v___x_3266_ = lean_st_ref_get(v___y_3239_);
v_env_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_ref(v_env_3267_);
lean_dec(v___x_3266_);
v___x_3268_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
v___x_3269_ = lean_array_fget(v_modules_3263_, v_val_3261_);
lean_dec(v_val_3261_);
lean_dec_ref(v_modules_3263_);
if (v_isMeta_3237_ == 0)
{
lean_dec_ref(v_env_3267_);
v___y_3271_ = v_isMeta_3237_;
goto v___jp_3270_;
}
else
{
uint8_t v___x_3282_; 
lean_inc(v_declName_3236_);
v___x_3282_ = l_Lean_isMarkedMeta(v_env_3267_, v_declName_3236_);
if (v___x_3282_ == 0)
{
v___y_3271_ = v_isMeta_3237_;
goto v___jp_3270_;
}
else
{
uint8_t v___x_3283_; 
v___x_3283_ = 0;
v___y_3271_ = v___x_3283_;
goto v___jp_3270_;
}
}
v___jp_3270_:
{
lean_object* v_toImport_3272_; lean_object* v_module_3273_; lean_object* v___x_3274_; 
v_toImport_3272_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_toImport_3272_);
lean_dec(v___x_3269_);
v_module_3273_ = lean_ctor_get(v_toImport_3272_, 0);
lean_inc(v_module_3273_);
lean_dec_ref(v_toImport_3272_);
lean_inc(v_declName_3236_);
v___x_3274_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3273_, v___y_3271_, v_declName_3236_, v___y_3238_, v___y_3239_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec_ref(v___x_3274_);
v___x_3275_ = l_Lean_indirectModUseExt;
v___x_3276_ = lean_box(1);
v___x_3277_ = lean_box(0);
lean_inc_ref(v_env_3245_);
v___x_3278_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3268_, v___x_3275_, v_env_3245_, v___x_3276_, v___x_3277_);
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_3278_, v_declName_3236_);
lean_dec(v___x_3278_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3));
v___y_3247_ = v___x_3280_;
goto v___jp_3246_;
}
else
{
lean_object* v_val_3281_; 
v_val_3281_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_val_3281_);
lean_dec_ref(v___x_3279_);
v___y_3247_ = v_val_3281_;
goto v___jp_3246_;
}
}
else
{
lean_dec_ref(v_env_3245_);
lean_dec(v_declName_3236_);
return v___x_3274_;
}
}
}
}
v___jp_3242_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
v___jp_3246_:
{
lean_object* v___x_3248_; size_t v_sz_3249_; size_t v___x_3250_; lean_object* v___x_3251_; 
v___x_3248_ = lean_box(0);
v_sz_3249_ = lean_array_size(v___y_3247_);
v___x_3250_ = ((size_t)0ULL);
v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_3245_, v_declName_3236_, v___y_3247_, v_sz_3249_, v___x_3250_, v___x_3248_, v___y_3238_, v___y_3239_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v_env_3245_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v___x_3251_, 0);
lean_dec(v_unused_3259_);
v___x_3253_ = v___x_3251_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v___x_3251_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3248_);
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3248_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
else
{
return v___x_3251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(lean_object* v_declName_3284_, lean_object* v_isMeta_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
uint8_t v_isMeta_boxed_3289_; lean_object* v_res_3290_; 
v_isMeta_boxed_3289_ = lean_unbox(v_isMeta_3285_);
v_res_3290_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_3284_, v_isMeta_boxed_3289_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
return v_res_3290_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8));
v___x_3308_ = l_Lean_stringToMessageData(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11);
v___x_3313_ = l_Lean_MessageData_note(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_box(0);
v___x_3323_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3324_ = l_Lean_mkConst(v___x_3323_, v___x_3322_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18));
v___x_3327_ = l_Lean_stringToMessageData(v___x_3326_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20));
v___x_3330_ = l_Lean_stringToMessageData(v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* v_x_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
lean_inc(v_x_3331_);
v___x_3385_ = l_Lean_Syntax_isOfKind(v_x_3331_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
lean_dec(v_x_3331_);
v___x_3386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3387_ = lean_unsigned_to_nat(0u);
v___x_3388_ = l_Lean_Syntax_getArg(v_x_3331_, v___x_3387_);
v___x_3389_ = lean_unsigned_to_nat(1u);
v___x_3390_ = l_Lean_Syntax_matchesNull(v___x_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_dec(v_x_3331_);
v___x_3391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3391_;
}
else
{
lean_object* v___x_3392_; lean_object* v_id_3393_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; uint8_t v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___x_3433_; uint8_t v___x_3434_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; 
v___x_3392_ = lean_unsigned_to_nat(2u);
v_id_3393_ = l_Lean_Syntax_getArg(v_x_3331_, v___x_3392_);
v___x_3433_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
lean_inc(v_id_3393_);
v___x_3434_ = l_Lean_Syntax_isOfKind(v_id_3393_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3462_; 
lean_dec(v_id_3393_);
lean_dec(v_x_3331_);
v___x_3462_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3462_;
}
else
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Elab_Command_getRef___redArg(v_a_3332_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v_fileName_3466_; lean_object* v_fileMap_3467_; lean_object* v_currRecDepth_3468_; lean_object* v_cmdPos_3469_; lean_object* v_macroStack_3470_; lean_object* v_quotContext_x3f_3471_; lean_object* v_currMacroScope_3472_; lean_object* v_snap_x3f_3473_; lean_object* v_cancelTk_x3f_3474_; uint8_t v_suppressElabErrors_3475_; lean_object* v_env_3476_; lean_object* v_cmd_3477_; lean_object* v___x_3478_; lean_object* v_t_3479_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v_ref_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3463_);
v___x_3465_ = lean_st_ref_get(v_a_3333_);
v_fileName_3466_ = lean_ctor_get(v_a_3332_, 0);
v_fileMap_3467_ = lean_ctor_get(v_a_3332_, 1);
v_currRecDepth_3468_ = lean_ctor_get(v_a_3332_, 2);
v_cmdPos_3469_ = lean_ctor_get(v_a_3332_, 3);
v_macroStack_3470_ = lean_ctor_get(v_a_3332_, 4);
v_quotContext_x3f_3471_ = lean_ctor_get(v_a_3332_, 5);
v_currMacroScope_3472_ = lean_ctor_get(v_a_3332_, 6);
v_snap_x3f_3473_ = lean_ctor_get(v_a_3332_, 8);
v_cancelTk_x3f_3474_ = lean_ctor_get(v_a_3332_, 9);
v_suppressElabErrors_3475_ = lean_ctor_get_uint8(v_a_3332_, sizeof(void*)*10);
v_env_3476_ = lean_ctor_get(v___x_3465_, 0);
lean_inc_ref(v_env_3476_);
lean_dec(v___x_3465_);
v_cmd_3477_ = l_Lean_Syntax_getArg(v_x_3331_, v___x_3389_);
v___x_3478_ = lean_unsigned_to_nat(3u);
v_t_3479_ = l_Lean_Syntax_getArg(v_x_3331_, v___x_3478_);
lean_dec(v_x_3331_);
v_ref_3505_ = l_Lean_replaceRef(v_cmd_3477_, v_a_3464_);
lean_dec(v_a_3464_);
lean_dec(v_cmd_3477_);
lean_inc(v_cancelTk_x3f_3474_);
lean_inc(v_snap_x3f_3473_);
lean_inc(v_currMacroScope_3472_);
lean_inc(v_quotContext_x3f_3471_);
lean_inc(v_macroStack_3470_);
lean_inc(v_cmdPos_3469_);
lean_inc(v_currRecDepth_3468_);
lean_inc_ref(v_fileMap_3467_);
lean_inc_ref(v_fileName_3466_);
v___x_3506_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3506_, 0, v_fileName_3466_);
lean_ctor_set(v___x_3506_, 1, v_fileMap_3467_);
lean_ctor_set(v___x_3506_, 2, v_currRecDepth_3468_);
lean_ctor_set(v___x_3506_, 3, v_cmdPos_3469_);
lean_ctor_set(v___x_3506_, 4, v_macroStack_3470_);
lean_ctor_set(v___x_3506_, 5, v_quotContext_x3f_3471_);
lean_ctor_set(v___x_3506_, 6, v_currMacroScope_3472_);
lean_ctor_set(v___x_3506_, 7, v_ref_3505_);
lean_ctor_set(v___x_3506_, 8, v_snap_x3f_3473_);
lean_ctor_set(v___x_3506_, 9, v_cancelTk_x3f_3474_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*10, v_suppressElabErrors_3475_);
v___x_3507_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3508_ = l_Lean_Environment_contains(v_env_3476_, v___x_3507_, v___x_3434_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec(v_t_3479_);
lean_dec(v_id_3393_);
v___x_3509_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
v___x_3510_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v___x_3509_, v___x_3506_, v_a_3333_);
lean_dec_ref(v___x_3506_);
return v___x_3510_;
}
else
{
v___y_3481_ = v___x_3506_;
v___y_3482_ = v_a_3333_;
goto v___jp_3480_;
}
v___jp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3484_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_3483_, v___x_3434_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; 
lean_dec_ref(v___x_3484_);
v___x_3485_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3486_, 0, v_t_3479_);
lean_closure_set(v___f_3486_, 1, v___x_3485_);
v___x_3487_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3486_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v___x_3487_);
v___x_3489_ = l_Lean_TSyntax_getId(v_id_3393_);
v___x_3490_ = l_Lean_Name_isAnonymous(v___x_3489_);
if (v___x_3490_ == 0)
{
v___y_3451_ = v_a_3488_;
v___y_3452_ = v___x_3489_;
v___y_3453_ = v___y_3481_;
v___y_3454_ = v___y_3482_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v___x_3489_);
lean_dec(v_a_3488_);
v___x_3491_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
lean_inc(v_id_3393_);
v___x_3492_ = l_Lean_MessageData_ofSyntax(v_id_3393_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3393_, v___x_3495_, v___y_3481_, v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_id_3393_);
return v___x_3496_;
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___y_3481_);
lean_dec(v_id_3393_);
v_a_3497_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3487_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3487_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_dec_ref(v___y_3481_);
lean_dec(v_t_3479_);
lean_dec(v_id_3393_);
return v___x_3484_;
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_id_3393_);
lean_dec(v_x_3331_);
v_a_3511_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3463_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3463_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
v___jp_3394_:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Syntax_getTailPos_x3f(v_id_3393_, v___y_3399_);
lean_dec(v_id_3393_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_inc(v___y_3401_);
v___y_3336_ = v___y_3396_;
v___y_3337_ = v___y_3395_;
v___y_3338_ = v___y_3398_;
v___y_3339_ = v___y_3397_;
v___y_3340_ = v___y_3401_;
v___y_3341_ = v___y_3400_;
v___y_3342_ = v___y_3401_;
goto v___jp_3335_;
}
else
{
lean_object* v_val_3403_; 
v_val_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_val_3403_);
lean_dec_ref(v___x_3402_);
v___y_3336_ = v___y_3396_;
v___y_3337_ = v___y_3395_;
v___y_3338_ = v___y_3398_;
v___y_3339_ = v___y_3397_;
v___y_3340_ = v___y_3401_;
v___y_3341_ = v___y_3400_;
v___y_3342_ = v_val_3403_;
goto v___jp_3335_;
}
}
v___jp_3404_:
{
lean_object* v_fileMap_3409_; uint8_t v___x_3410_; lean_object* v___x_3411_; 
v_fileMap_3409_ = lean_ctor_get(v___y_3407_, 1);
lean_inc_ref(v_fileMap_3409_);
v___x_3410_ = 0;
v___x_3411_ = l_Lean_Syntax_getPos_x3f(v_id_3393_, v___x_3410_);
if (lean_obj_tag(v___x_3411_) == 0)
{
v___y_3395_ = v___y_3408_;
v___y_3396_ = v___y_3405_;
v___y_3397_ = v___y_3407_;
v___y_3398_ = v___y_3406_;
v___y_3399_ = v___x_3410_;
v___y_3400_ = v_fileMap_3409_;
v___y_3401_ = v___x_3387_;
goto v___jp_3394_;
}
else
{
lean_object* v_val_3412_; 
v_val_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_val_3412_);
lean_dec_ref(v___x_3411_);
v___y_3395_ = v___y_3408_;
v___y_3396_ = v___y_3405_;
v___y_3397_ = v___y_3407_;
v___y_3398_ = v___y_3406_;
v___y_3399_ = v___x_3410_;
v___y_3400_ = v_fileMap_3409_;
v___y_3401_ = v_val_3412_;
goto v___jp_3394_;
}
}
v___jp_3413_:
{
lean_object* v___x_3418_; lean_object* v_env_3419_; lean_object* v___x_3420_; lean_object* v_toEnvExtension_3421_; lean_object* v_asyncMode_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3418_ = lean_st_ref_get(v___y_3417_);
v_env_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_ref(v_env_3419_);
lean_dec(v___x_3418_);
v___x_3420_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3421_ = lean_ctor_get(v___x_3420_, 0);
v_asyncMode_3422_ = lean_ctor_get(v_toEnvExtension_3421_, 2);
v___x_3423_ = lean_box(1);
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3423_, v___x_3420_, v_env_3419_, v_asyncMode_3422_, v___x_3424_);
v___x_3426_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_3415_, v___x_3425_);
lean_dec(v___x_3425_);
if (v___x_3426_ == 0)
{
v___y_3405_ = v___y_3414_;
v___y_3406_ = v___y_3415_;
v___y_3407_ = v___y_3416_;
v___y_3408_ = v___y_3417_;
goto v___jp_3404_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_dec_ref(v___y_3414_);
v___x_3427_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
v___x_3428_ = l_Lean_MessageData_ofName(v___y_3415_);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3393_, v___x_3431_, v___y_3416_, v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v_id_3393_);
return v___x_3432_;
}
}
v___jp_3435_:
{
lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = l_Lean_Name_getNumParts(v___y_3437_);
v___x_3441_ = lean_nat_dec_eq(v___x_3440_, v___x_3392_);
lean_dec(v___x_3440_);
if (v___x_3441_ == 0)
{
if (v___x_3434_ == 0)
{
v___y_3414_ = v___y_3436_;
v___y_3415_ = v___y_3437_;
v___y_3416_ = v___y_3438_;
v___y_3417_ = v___y_3439_;
goto v___jp_3413_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec_ref(v___y_3436_);
v___x_3442_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
v___x_3443_ = l_Lean_MessageData_ofName(v___y_3437_);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3393_, v___x_3448_, v___y_3438_, v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v_id_3393_);
return v___x_3449_;
}
}
else
{
v___y_3414_ = v___y_3436_;
v___y_3415_ = v___y_3437_;
v___y_3416_ = v___y_3438_;
v___y_3417_ = v___y_3439_;
goto v___jp_3413_;
}
}
v___jp_3450_:
{
uint8_t v___x_3455_; 
v___x_3455_ = l_Lean_Name_hasMacroScopes(v___y_3452_);
if (v___x_3455_ == 0)
{
v___y_3436_ = v___y_3451_;
v___y_3437_ = v___y_3452_;
v___y_3438_ = v___y_3453_;
v___y_3439_ = v___y_3454_;
goto v___jp_3435_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
v___x_3456_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
lean_inc(v_id_3393_);
v___x_3457_ = l_Lean_MessageData_ofSyntax(v_id_3393_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3393_, v___x_3460_, v___y_3453_, v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v_id_3393_);
return v___x_3461_;
}
}
}
}
v___jp_3335_:
{
lean_object* v___x_3343_; lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v___y_3339_);
v___x_3343_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_3337_);
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3383_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3383_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v_env_3349_; lean_object* v_messages_3350_; lean_object* v_scopes_3351_; lean_object* v_usedQuotCtxts_3352_; lean_object* v_nextMacroScope_3353_; lean_object* v_maxRecDepth_3354_; lean_object* v_ngen_3355_; lean_object* v_auxDeclNGen_3356_; lean_object* v_infoState_3357_; lean_object* v_traceState_3358_; lean_object* v_snapshotTasks_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3382_; 
v___x_3348_ = lean_st_ref_take(v___y_3337_);
v_env_3349_ = lean_ctor_get(v___x_3348_, 0);
v_messages_3350_ = lean_ctor_get(v___x_3348_, 1);
v_scopes_3351_ = lean_ctor_get(v___x_3348_, 2);
v_usedQuotCtxts_3352_ = lean_ctor_get(v___x_3348_, 3);
v_nextMacroScope_3353_ = lean_ctor_get(v___x_3348_, 4);
v_maxRecDepth_3354_ = lean_ctor_get(v___x_3348_, 5);
v_ngen_3355_ = lean_ctor_get(v___x_3348_, 6);
v_auxDeclNGen_3356_ = lean_ctor_get(v___x_3348_, 7);
v_infoState_3357_ = lean_ctor_get(v___x_3348_, 8);
v_traceState_3358_ = lean_ctor_get(v___x_3348_, 9);
v_snapshotTasks_3359_ = lean_ctor_get(v___x_3348_, 10);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3361_ = v___x_3348_;
v_isShared_3362_ = v_isSharedCheck_3382_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_snapshotTasks_3359_);
lean_inc(v_traceState_3358_);
lean_inc(v_infoState_3357_);
lean_inc(v_auxDeclNGen_3356_);
lean_inc(v_ngen_3355_);
lean_inc(v_maxRecDepth_3354_);
lean_inc(v_nextMacroScope_3353_);
lean_inc(v_usedQuotCtxts_3352_);
lean_inc(v_scopes_3351_);
lean_inc(v_messages_3350_);
lean_inc(v_env_3349_);
lean_dec(v___x_3348_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3382_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v_toEnvExtension_3364_; lean_object* v_asyncMode_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3363_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3364_ = lean_ctor_get(v___x_3363_, 0);
v_asyncMode_3365_ = lean_ctor_get(v_toEnvExtension_3364_, 2);
v___x_3366_ = l_Lean_DeclarationRange_ofStringPositions(v___y_3341_, v___y_3340_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec(v___y_3340_);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_a_3344_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
v___x_3369_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v___y_3336_);
lean_ctor_set(v___x_3370_, 2, v___x_3368_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___y_3338_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_box(0);
v___x_3373_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3363_, v_env_3349_, v___x_3371_, v_asyncMode_3365_, v___x_3372_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3373_);
v___x_3375_ = v___x_3361_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_messages_3350_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_scopes_3351_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_usedQuotCtxts_3352_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v_nextMacroScope_3353_);
lean_ctor_set(v_reuseFailAlloc_3381_, 5, v_maxRecDepth_3354_);
lean_ctor_set(v_reuseFailAlloc_3381_, 6, v_ngen_3355_);
lean_ctor_set(v_reuseFailAlloc_3381_, 7, v_auxDeclNGen_3356_);
lean_ctor_set(v_reuseFailAlloc_3381_, 8, v_infoState_3357_);
lean_ctor_set(v_reuseFailAlloc_3381_, 9, v_traceState_3358_);
lean_ctor_set(v_reuseFailAlloc_3381_, 10, v_snapshotTasks_3359_);
v___x_3375_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3376_ = lean_st_ref_set(v___y_3337_, v___x_3375_);
v___x_3377_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3377_);
v___x_3379_ = v___x_3346_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object* v_x_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_3519_, v_a_3520_, v_a_3521_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object* v_00_u03b1_3524_, lean_object* v_ref_3525_, lean_object* v_msg_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_3525_, v_msg_3526_, v___y_3527_, v___y_3528_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object* v_00_u03b1_3531_, lean_object* v_ref_3532_, lean_object* v_msg_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v_00_u03b1_3531_, v_ref_3532_, v_msg_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v_ref_3532_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(lean_object* v_msgData_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_3538_, v___y_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(lean_object* v_msgData_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(v_msgData_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object* v_00_u03b1_3548_, lean_object* v_msg_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_3549_, v___y_3550_, v___y_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object* v_00_u03b1_3554_, lean_object* v_msg_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(v_00_u03b1_3554_, v_msg_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(lean_object* v_msgData_3560_, lean_object* v_macroStack_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_3560_, v_macroStack_3561_, v___y_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(lean_object* v_msgData_3566_, lean_object* v_macroStack_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(v_msgData_3566_, v_macroStack_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3579_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3580_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1));
v___x_3582_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
v___x_3583_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3579_, v___x_3580_, v___x_3581_, v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
return v_res_3585_;
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
