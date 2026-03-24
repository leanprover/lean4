// Lean compiler output
// Module: Lean.Elab.ErrorExplanation
// Imports: public import Lean.Widget.UserWidget
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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
extern lean_object* l_Lean_errorDescriptionWidget;
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*);
static const lean_string_object l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0 = (const lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value;
static const lean_string_object l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "errorDescriptionWidget"};
static const lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1 = (const lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value;
static const lean_ctor_object l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(97, 213, 240, 52, 84, 173, 13, 164)}};
static const lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2 = (const lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "throwNamedErrorMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(147, 71, 28, 75, 97, 117, 128, 98)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwNamedErrorAtMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(123, 65, 2, 235, 170, 76, 164, 46)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "logNamedErrorMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value),LEAN_SCALAR_PTR_LITERAL(73, 64, 162, 114, 236, 8, 247, 133)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "logNamedErrorAtMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 239, 95, 34, 175, 88, 94, 179)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "logNamedWarningMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value),LEAN_SCALAR_PTR_LITERAL(2, 91, 200, 35, 216, 48, 104, 184)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "logNamedWarningAtMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.logNamedWarning"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "logNamedWarning"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value),LEAN_SCALAR_PTR_LITERAL(34, 53, 86, 106, 208, 200, 15, 240)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.logNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "logNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value),LEAN_SCALAR_PTR_LITERAL(215, 212, 218, 121, 130, 143, 154, 83)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.logNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "logNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value),LEAN_SCALAR_PTR_LITERAL(193, 48, 226, 102, 122, 31, 140, 200)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.throwNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "throwNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value),LEAN_SCALAR_PTR_LITERAL(151, 5, 168, 142, 232, 160, 229, 118)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.throwNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "throwNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value),LEAN_SCALAR_PTR_LITERAL(55, 87, 79, 197, 235, 27, 154, 123)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 208, 119, 110, 215, 6, 136, 235)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value;
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Log"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 176, 165, 28, 129, 118, 207, 221)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value)}};
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ErrorExplanation"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabCheckedNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 18, 113, 52, 22, 68, 187, 184)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 92, 138, 205, 69, 125, 159, 73)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(150, 121, 11, 220, 201, 134, 39, 253)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Cannot add explanation: An error explanation already exists for `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid name `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "`: Error explanation names must have two components"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = "The first component of an error explanation name identifies the package from which the error originates, and the second identifies the error itself."};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "`: Error explanations cannot have inaccessible names. This error often occurs when an error explanation is generated using a macro."};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Metadata"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 124, 72, 60, 38, 86, 32, 253)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(228, 194, 107, 149, 38, 116, 86, 230)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid name for error explanation: `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "To use this command, add `import Lean.ErrorExplanation` to the header of this file"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "elabRegisterErrorExplanation"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 18, 113, 52, 22, 68, 187, 184)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 148, 59, 123, 129, 88, 83, 38)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2));
v___x_8_ = l_Lean_errorDescriptionWidget;
v___x_9_ = l_Lean_Widget_addBuiltinModule(v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
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
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_82_ = l_String_toRawSubstring_x27(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41));
v___x_108_ = l_String_toRawSubstring_x27(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47));
v___x_121_ = l_String_toRawSubstring_x27(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55));
v___x_137_ = l_String_toRawSubstring_x27(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
lean_inc(v_x_148_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_x_148_);
v___x_154_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
lean_inc(v_x_148_);
v___x_156_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_x_148_);
v___x_158_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
lean_inc(v_x_148_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_x_148_);
v___x_162_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_163_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_unsigned_to_nat(3u);
v___x_166_ = l_Lean_Syntax_getArg(v_x_148_, v___x_165_);
v___x_167_ = l_Lean_Syntax_matchesNull(v___x_166_, v___x_164_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_168_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_id_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_148_, v___x_169_);
v___x_171_ = lean_unsigned_to_nat(2u);
v_id_172_ = l_Lean_Syntax_getArg(v_x_148_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(4u);
v___x_174_ = l_Lean_Syntax_getArg(v_x_148_, v___x_173_);
lean_dec(v_x_148_);
v___x_175_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_174_);
v___x_176_ = l_Lean_Syntax_isOfKind(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v_quotContext_177_; lean_object* v_currMacroScope_178_; lean_object* v_ref_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_quotContext_177_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_177_);
v_currMacroScope_178_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_178_);
v_ref_179_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_179_);
lean_dec_ref(v_a_149_);
v___x_180_ = l_Lean_SourceInfo_fromRef(v_ref_179_, v___x_176_);
lean_dec(v_ref_179_);
v___x_181_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_182_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
v___x_183_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21));
v___x_184_ = l_Lean_addMacroScope(v_quotContext_177_, v___x_183_, v_currMacroScope_178_);
v___x_185_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23));
lean_inc(v___x_180_);
v___x_186_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_186_, 0, v___x_180_);
lean_ctor_set(v___x_186_, 1, v___x_182_);
lean_ctor_set(v___x_186_, 2, v___x_184_);
lean_ctor_set(v___x_186_, 3, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_188_ = l_Lean_TSyntax_getId(v_id_172_);
lean_dec(v_id_172_);
v___x_189_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_188_);
lean_inc(v___x_180_);
v___x_190_ = l_Lean_Syntax_node3(v___x_180_, v___x_187_, v___x_170_, v___x_189_, v___x_174_);
v___x_191_ = l_Lean_Syntax_node2(v___x_180_, v___x_181_, v___x_186_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_a_150_);
return v___x_192_;
}
else
{
lean_object* v_quotContext_193_; lean_object* v_currMacroScope_194_; lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_quotContext_193_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_193_);
v_currMacroScope_194_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_194_);
v_ref_195_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_195_);
lean_dec_ref(v_a_149_);
v___x_196_ = l_Lean_SourceInfo_fromRef(v_ref_195_, v___x_160_);
lean_dec(v_ref_195_);
v___x_197_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_198_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
v___x_199_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21));
v___x_200_ = l_Lean_addMacroScope(v_quotContext_193_, v___x_199_, v_currMacroScope_194_);
v___x_201_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23));
lean_inc(v___x_196_);
v___x_202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_202_, 0, v___x_196_);
lean_ctor_set(v___x_202_, 1, v___x_198_);
lean_ctor_set(v___x_202_, 2, v___x_200_);
lean_ctor_set(v___x_202_, 3, v___x_201_);
v___x_203_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_204_ = l_Lean_TSyntax_getId(v_id_172_);
lean_dec(v_id_172_);
v___x_205_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_207_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
lean_inc(v___x_196_);
v___x_208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_196_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_inc(v___x_196_);
v___x_209_ = l_Lean_Syntax_node2(v___x_196_, v___x_206_, v___x_208_, v___x_174_);
lean_inc(v___x_196_);
v___x_210_ = l_Lean_Syntax_node3(v___x_196_, v___x_203_, v___x_170_, v___x_205_, v___x_209_);
v___x_211_ = l_Lean_Syntax_node2(v___x_196_, v___x_197_, v___x_202_, v___x_210_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_150_);
return v___x_212_;
}
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_unsigned_to_nat(2u);
v___x_215_ = l_Lean_Syntax_getArg(v_x_148_, v___x_214_);
v___x_216_ = l_Lean_Syntax_matchesNull(v___x_215_, v___x_213_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_217_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v_id_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v_id_219_ = l_Lean_Syntax_getArg(v_x_148_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(3u);
v___x_221_ = l_Lean_Syntax_getArg(v_x_148_, v___x_220_);
lean_dec(v_x_148_);
v___x_222_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_221_);
v___x_223_ = l_Lean_Syntax_isOfKind(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v_quotContext_224_; lean_object* v_currMacroScope_225_; lean_object* v_ref_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_quotContext_224_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_224_);
v_currMacroScope_225_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_225_);
v_ref_226_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_226_);
lean_dec_ref(v_a_149_);
v___x_227_ = l_Lean_SourceInfo_fromRef(v_ref_226_, v___x_223_);
lean_dec(v_ref_226_);
v___x_228_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_229_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30);
v___x_230_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
v___x_231_ = l_Lean_addMacroScope(v_quotContext_224_, v___x_230_, v_currMacroScope_225_);
v___x_232_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34));
lean_inc(v___x_227_);
v___x_233_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_233_, 0, v___x_227_);
lean_ctor_set(v___x_233_, 1, v___x_229_);
lean_ctor_set(v___x_233_, 2, v___x_231_);
lean_ctor_set(v___x_233_, 3, v___x_232_);
v___x_234_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_235_ = l_Lean_TSyntax_getId(v_id_219_);
lean_dec(v_id_219_);
v___x_236_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_235_);
lean_inc(v___x_227_);
v___x_237_ = l_Lean_Syntax_node2(v___x_227_, v___x_234_, v___x_236_, v___x_221_);
v___x_238_ = l_Lean_Syntax_node2(v___x_227_, v___x_228_, v___x_233_, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_150_);
return v___x_239_;
}
else
{
lean_object* v_quotContext_240_; lean_object* v_currMacroScope_241_; lean_object* v_ref_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_quotContext_240_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_240_);
v_currMacroScope_241_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_241_);
v_ref_242_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_242_);
lean_dec_ref(v_a_149_);
v___x_243_ = l_Lean_SourceInfo_fromRef(v_ref_242_, v___x_158_);
lean_dec(v_ref_242_);
v___x_244_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_245_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30);
v___x_246_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
v___x_247_ = l_Lean_addMacroScope(v_quotContext_240_, v___x_246_, v_currMacroScope_241_);
v___x_248_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34));
lean_inc(v___x_243_);
v___x_249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_249_, 0, v___x_243_);
lean_ctor_set(v___x_249_, 1, v___x_245_);
lean_ctor_set(v___x_249_, 2, v___x_247_);
lean_ctor_set(v___x_249_, 3, v___x_248_);
v___x_250_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_251_ = l_Lean_TSyntax_getId(v_id_219_);
lean_dec(v_id_219_);
v___x_252_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_254_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
lean_inc(v___x_243_);
v___x_255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_243_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_inc(v___x_243_);
v___x_256_ = l_Lean_Syntax_node2(v___x_243_, v___x_253_, v___x_255_, v___x_221_);
lean_inc(v___x_243_);
v___x_257_ = l_Lean_Syntax_node2(v___x_243_, v___x_250_, v___x_252_, v___x_256_);
v___x_258_ = l_Lean_Syntax_node2(v___x_243_, v___x_244_, v___x_249_, v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_a_150_);
return v___x_259_;
}
}
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_unsigned_to_nat(3u);
v___x_262_ = l_Lean_Syntax_getArg(v_x_148_, v___x_261_);
v___x_263_ = l_Lean_Syntax_matchesNull(v___x_262_, v___x_260_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_264_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_id_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = l_Lean_Syntax_getArg(v_x_148_, v___x_265_);
v___x_267_ = lean_unsigned_to_nat(2u);
v_id_268_ = l_Lean_Syntax_getArg(v_x_148_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(4u);
v___x_270_ = l_Lean_Syntax_getArg(v_x_148_, v___x_269_);
lean_dec(v_x_148_);
v___x_271_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_270_);
v___x_272_ = l_Lean_Syntax_isOfKind(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v_quotContext_273_; lean_object* v_currMacroScope_274_; lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_quotContext_273_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_273_);
v_currMacroScope_274_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_274_);
v_ref_275_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_275_);
lean_dec_ref(v_a_149_);
v___x_276_ = l_Lean_SourceInfo_fromRef(v_ref_275_, v___x_272_);
lean_dec(v_ref_275_);
v___x_277_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_278_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36);
v___x_279_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38));
v___x_280_ = l_Lean_addMacroScope(v_quotContext_273_, v___x_279_, v_currMacroScope_274_);
v___x_281_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40));
lean_inc(v___x_276_);
v___x_282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_282_, 0, v___x_276_);
lean_ctor_set(v___x_282_, 1, v___x_278_);
lean_ctor_set(v___x_282_, 2, v___x_280_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
v___x_283_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_284_ = l_Lean_TSyntax_getId(v_id_268_);
lean_dec(v_id_268_);
v___x_285_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_284_);
lean_inc(v___x_276_);
v___x_286_ = l_Lean_Syntax_node3(v___x_276_, v___x_283_, v___x_266_, v___x_285_, v___x_270_);
v___x_287_ = l_Lean_Syntax_node2(v___x_276_, v___x_277_, v___x_282_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_150_);
return v___x_288_;
}
else
{
lean_object* v_quotContext_289_; lean_object* v_currMacroScope_290_; lean_object* v_ref_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_quotContext_289_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_289_);
v_currMacroScope_290_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_290_);
v_ref_291_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_291_);
lean_dec_ref(v_a_149_);
v___x_292_ = l_Lean_SourceInfo_fromRef(v_ref_291_, v___x_156_);
lean_dec(v_ref_291_);
v___x_293_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_294_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36);
v___x_295_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38));
v___x_296_ = l_Lean_addMacroScope(v_quotContext_289_, v___x_295_, v_currMacroScope_290_);
v___x_297_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40));
lean_inc(v___x_292_);
v___x_298_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_298_, 0, v___x_292_);
lean_ctor_set(v___x_298_, 1, v___x_294_);
lean_ctor_set(v___x_298_, 2, v___x_296_);
lean_ctor_set(v___x_298_, 3, v___x_297_);
v___x_299_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_300_ = l_Lean_TSyntax_getId(v_id_268_);
lean_dec(v_id_268_);
v___x_301_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_300_);
v___x_302_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_303_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
lean_inc(v___x_292_);
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_292_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc(v___x_292_);
v___x_305_ = l_Lean_Syntax_node2(v___x_292_, v___x_302_, v___x_304_, v___x_270_);
lean_inc(v___x_292_);
v___x_306_ = l_Lean_Syntax_node3(v___x_292_, v___x_299_, v___x_266_, v___x_301_, v___x_305_);
v___x_307_ = l_Lean_Syntax_node2(v___x_292_, v___x_293_, v___x_298_, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_a_150_);
return v___x_308_;
}
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_unsigned_to_nat(2u);
v___x_311_ = l_Lean_Syntax_getArg(v_x_148_, v___x_310_);
v___x_312_ = l_Lean_Syntax_matchesNull(v___x_311_, v___x_309_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_313_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v_id_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v_id_315_ = l_Lean_Syntax_getArg(v_x_148_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(3u);
v___x_317_ = l_Lean_Syntax_getArg(v_x_148_, v___x_316_);
lean_dec(v_x_148_);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_317_);
v___x_319_ = l_Lean_Syntax_isOfKind(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v_quotContext_320_; lean_object* v_currMacroScope_321_; lean_object* v_ref_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_quotContext_320_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_320_);
v_currMacroScope_321_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_321_);
v_ref_322_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_322_);
lean_dec_ref(v_a_149_);
v___x_323_ = l_Lean_SourceInfo_fromRef(v_ref_322_, v___x_319_);
lean_dec(v_ref_322_);
v___x_324_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_325_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42);
v___x_326_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44));
v___x_327_ = l_Lean_addMacroScope(v_quotContext_320_, v___x_326_, v_currMacroScope_321_);
v___x_328_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46));
lean_inc(v___x_323_);
v___x_329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_329_, 0, v___x_323_);
lean_ctor_set(v___x_329_, 1, v___x_325_);
lean_ctor_set(v___x_329_, 2, v___x_327_);
lean_ctor_set(v___x_329_, 3, v___x_328_);
v___x_330_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_331_ = l_Lean_TSyntax_getId(v_id_315_);
lean_dec(v_id_315_);
v___x_332_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_331_);
lean_inc(v___x_323_);
v___x_333_ = l_Lean_Syntax_node2(v___x_323_, v___x_330_, v___x_332_, v___x_317_);
v___x_334_ = l_Lean_Syntax_node2(v___x_323_, v___x_324_, v___x_329_, v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_150_);
return v___x_335_;
}
else
{
lean_object* v_quotContext_336_; lean_object* v_currMacroScope_337_; lean_object* v_ref_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_quotContext_336_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_336_);
v_currMacroScope_337_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_337_);
v_ref_338_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_338_);
lean_dec_ref(v_a_149_);
v___x_339_ = l_Lean_SourceInfo_fromRef(v_ref_338_, v___x_154_);
lean_dec(v_ref_338_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_341_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42);
v___x_342_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44));
v___x_343_ = l_Lean_addMacroScope(v_quotContext_336_, v___x_342_, v_currMacroScope_337_);
v___x_344_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46));
lean_inc(v___x_339_);
v___x_345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_345_, 0, v___x_339_);
lean_ctor_set(v___x_345_, 1, v___x_341_);
lean_ctor_set(v___x_345_, 2, v___x_343_);
lean_ctor_set(v___x_345_, 3, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_347_ = l_Lean_TSyntax_getId(v_id_315_);
lean_dec(v_id_315_);
v___x_348_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_350_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
lean_inc(v___x_339_);
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_339_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
lean_inc(v___x_339_);
v___x_352_ = l_Lean_Syntax_node2(v___x_339_, v___x_349_, v___x_351_, v___x_317_);
lean_inc(v___x_339_);
v___x_353_ = l_Lean_Syntax_node2(v___x_339_, v___x_346_, v___x_348_, v___x_352_);
v___x_354_ = l_Lean_Syntax_node2(v___x_339_, v___x_340_, v___x_345_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_150_);
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_unsigned_to_nat(3u);
v___x_358_ = l_Lean_Syntax_getArg(v_x_148_, v___x_357_);
v___x_359_ = l_Lean_Syntax_matchesNull(v___x_358_, v___x_356_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_360_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_id_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = l_Lean_Syntax_getArg(v_x_148_, v___x_361_);
v___x_363_ = lean_unsigned_to_nat(2u);
v_id_364_ = l_Lean_Syntax_getArg(v_x_148_, v___x_363_);
v___x_365_ = lean_unsigned_to_nat(4u);
v___x_366_ = l_Lean_Syntax_getArg(v_x_148_, v___x_365_);
lean_dec(v_x_148_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_366_);
v___x_368_ = l_Lean_Syntax_isOfKind(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v_quotContext_369_; lean_object* v_currMacroScope_370_; lean_object* v_ref_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_quotContext_369_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_369_);
v_currMacroScope_370_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_370_);
v_ref_371_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_371_);
lean_dec_ref(v_a_149_);
v___x_372_ = l_Lean_SourceInfo_fromRef(v_ref_371_, v___x_368_);
lean_dec(v_ref_371_);
v___x_373_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_374_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48);
v___x_375_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50));
v___x_376_ = l_Lean_addMacroScope(v_quotContext_369_, v___x_375_, v_currMacroScope_370_);
v___x_377_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52));
lean_inc(v___x_372_);
v___x_378_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_378_, 0, v___x_372_);
lean_ctor_set(v___x_378_, 1, v___x_374_);
lean_ctor_set(v___x_378_, 2, v___x_376_);
lean_ctor_set(v___x_378_, 3, v___x_377_);
v___x_379_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_380_ = l_Lean_TSyntax_getId(v_id_364_);
lean_dec(v_id_364_);
v___x_381_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_380_);
lean_inc(v___x_372_);
v___x_382_ = l_Lean_Syntax_node3(v___x_372_, v___x_379_, v___x_362_, v___x_381_, v___x_366_);
v___x_383_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_378_, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_a_150_);
return v___x_384_;
}
else
{
lean_object* v_quotContext_385_; lean_object* v_currMacroScope_386_; lean_object* v_ref_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_quotContext_385_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_385_);
v_currMacroScope_386_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_386_);
v_ref_387_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_387_);
lean_dec_ref(v_a_149_);
v___x_388_ = l_Lean_SourceInfo_fromRef(v_ref_387_, v___x_152_);
lean_dec(v_ref_387_);
v___x_389_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_390_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48);
v___x_391_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50));
v___x_392_ = l_Lean_addMacroScope(v_quotContext_385_, v___x_391_, v_currMacroScope_386_);
v___x_393_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52));
lean_inc(v___x_388_);
v___x_394_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_394_, 0, v___x_388_);
lean_ctor_set(v___x_394_, 1, v___x_390_);
lean_ctor_set(v___x_394_, 2, v___x_392_);
lean_ctor_set(v___x_394_, 3, v___x_393_);
v___x_395_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_396_ = l_Lean_TSyntax_getId(v_id_364_);
lean_dec(v_id_364_);
v___x_397_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_396_);
v___x_398_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_399_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
lean_inc(v___x_388_);
v___x_400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_388_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
lean_inc(v___x_388_);
v___x_401_ = l_Lean_Syntax_node2(v___x_388_, v___x_398_, v___x_400_, v___x_366_);
lean_inc(v___x_388_);
v___x_402_ = l_Lean_Syntax_node3(v___x_388_, v___x_395_, v___x_362_, v___x_397_, v___x_401_);
v___x_403_ = l_Lean_Syntax_node2(v___x_388_, v___x_389_, v___x_394_, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_150_);
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_id_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_unsigned_to_nat(1u);
v_id_407_ = l_Lean_Syntax_getArg(v_x_148_, v___x_406_);
v___x_408_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54));
lean_inc(v_id_407_);
v___x_409_ = l_Lean_Syntax_isOfKind(v_id_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(2u);
v___x_411_ = l_Lean_Syntax_getArg(v_x_148_, v___x_410_);
v___x_412_ = l_Lean_Syntax_matchesNull(v___x_411_, v___x_405_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec(v_id_407_);
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_413_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_413_;
}
else
{
lean_object* v_quotContext_414_; lean_object* v_currMacroScope_415_; lean_object* v_ref_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_quotContext_414_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_414_);
v_currMacroScope_415_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_415_);
v_ref_416_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_416_);
lean_dec_ref(v_a_149_);
v___x_417_ = lean_unsigned_to_nat(3u);
v___x_418_ = l_Lean_Syntax_getArg(v_x_148_, v___x_417_);
lean_dec(v_x_148_);
v___x_419_ = l_Lean_SourceInfo_fromRef(v_ref_416_, v___x_409_);
lean_dec(v_ref_416_);
v___x_420_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_421_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56);
v___x_422_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
v___x_423_ = l_Lean_addMacroScope(v_quotContext_414_, v___x_422_, v_currMacroScope_415_);
v___x_424_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60));
lean_inc(v___x_419_);
v___x_425_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_425_, 0, v___x_419_);
lean_ctor_set(v___x_425_, 1, v___x_421_);
lean_ctor_set(v___x_425_, 2, v___x_423_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_427_ = l_Lean_TSyntax_getId(v_id_407_);
lean_dec(v_id_407_);
v___x_428_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_427_);
lean_inc(v___x_419_);
v___x_429_ = l_Lean_Syntax_node2(v___x_419_, v___x_426_, v___x_428_, v___x_418_);
v___x_430_ = l_Lean_Syntax_node2(v___x_419_, v___x_420_, v___x_425_, v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_a_150_);
return v___x_431_;
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(2u);
v___x_433_ = l_Lean_Syntax_getArg(v_x_148_, v___x_432_);
v___x_434_ = l_Lean_Syntax_matchesNull(v___x_433_, v___x_405_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_id_407_);
lean_dec_ref(v_a_149_);
lean_dec(v_x_148_);
v___x_435_ = l_Lean_Macro_throwUnsupported___redArg(v_a_150_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_436_ = lean_unsigned_to_nat(3u);
v___x_437_ = l_Lean_Syntax_getArg(v_x_148_, v___x_436_);
lean_dec(v_x_148_);
v___x_438_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_437_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v_quotContext_440_; lean_object* v_currMacroScope_441_; lean_object* v_ref_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_quotContext_440_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_440_);
v_currMacroScope_441_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_441_);
v_ref_442_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_442_);
lean_dec_ref(v_a_149_);
v___x_443_ = l_Lean_SourceInfo_fromRef(v_ref_442_, v___x_439_);
lean_dec(v_ref_442_);
v___x_444_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_445_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56);
v___x_446_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
v___x_447_ = l_Lean_addMacroScope(v_quotContext_440_, v___x_446_, v_currMacroScope_441_);
v___x_448_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60));
lean_inc(v___x_443_);
v___x_449_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_449_, 0, v___x_443_);
lean_ctor_set(v___x_449_, 1, v___x_445_);
lean_ctor_set(v___x_449_, 2, v___x_447_);
lean_ctor_set(v___x_449_, 3, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_451_ = l_Lean_TSyntax_getId(v_id_407_);
lean_dec(v_id_407_);
v___x_452_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_451_);
lean_inc(v___x_443_);
v___x_453_ = l_Lean_Syntax_node2(v___x_443_, v___x_450_, v___x_452_, v___x_437_);
v___x_454_ = l_Lean_Syntax_node2(v___x_443_, v___x_444_, v___x_449_, v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_a_150_);
return v___x_455_;
}
else
{
lean_object* v_quotContext_456_; lean_object* v_currMacroScope_457_; lean_object* v_ref_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_quotContext_456_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_quotContext_456_);
v_currMacroScope_457_ = lean_ctor_get(v_a_149_, 2);
lean_inc(v_currMacroScope_457_);
v_ref_458_ = lean_ctor_get(v_a_149_, 5);
lean_inc(v_ref_458_);
lean_dec_ref(v_a_149_);
v___x_459_ = 0;
v___x_460_ = l_Lean_SourceInfo_fromRef(v_ref_458_, v___x_459_);
lean_dec(v_ref_458_);
v___x_461_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_462_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56);
v___x_463_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
v___x_464_ = l_Lean_addMacroScope(v_quotContext_456_, v___x_463_, v_currMacroScope_457_);
v___x_465_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60));
lean_inc(v___x_460_);
v___x_466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_466_, 0, v___x_460_);
lean_ctor_set(v___x_466_, 1, v___x_462_);
lean_ctor_set(v___x_466_, 2, v___x_464_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
v___x_467_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_468_ = l_Lean_TSyntax_getId(v_id_407_);
lean_dec(v_id_407_);
v___x_469_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_468_);
v___x_470_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_471_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
lean_inc(v___x_460_);
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_460_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_inc(v___x_460_);
v___x_473_ = l_Lean_Syntax_node2(v___x_460_, v___x_470_, v___x_472_, v___x_437_);
lean_inc(v___x_460_);
v___x_474_ = l_Lean_Syntax_node2(v___x_460_, v___x_467_, v___x_469_, v___x_473_);
v___x_475_ = l_Lean_Syntax_node2(v___x_460_, v___x_461_, v___x_466_, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_a_150_);
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_477_, lean_object* v_b_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_dec(v_b_478_);
lean_dec(v_a_477_);
return v_x_479_;
}
else
{
lean_object* v_key_480_; lean_object* v_value_481_; lean_object* v_tail_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_494_; 
v_key_480_ = lean_ctor_get(v_x_479_, 0);
v_value_481_ = lean_ctor_get(v_x_479_, 1);
v_tail_482_ = lean_ctor_get(v_x_479_, 2);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_494_ == 0)
{
v___x_484_ = v_x_479_;
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_tail_482_);
lean_inc(v_value_481_);
lean_inc(v_key_480_);
lean_dec(v_x_479_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; 
v___x_486_ = lean_name_eq(v_key_480_, v_a_477_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_477_, v_b_478_, v_tail_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 2, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_key_480_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_value_481_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v_value_481_);
lean_dec(v_key_480_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v_b_478_);
lean_ctor_set(v___x_484_, 0, v_a_477_);
v___x_492_ = v___x_484_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_b_478_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_tail_482_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_495_; uint64_t v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(1723u);
v___x_496_ = lean_uint64_of_nat(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
return v_x_497_;
}
else
{
lean_object* v_key_499_; lean_object* v_value_500_; lean_object* v_tail_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_527_; 
v_key_499_ = lean_ctor_get(v_x_498_, 0);
v_value_500_ = lean_ctor_get(v_x_498_, 1);
v_tail_501_ = lean_ctor_get(v_x_498_, 2);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_527_ == 0)
{
v___x_503_ = v_x_498_;
v_isShared_504_ = v_isSharedCheck_527_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_tail_501_);
lean_inc(v_value_500_);
lean_inc(v_key_499_);
lean_dec(v_x_498_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_527_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint64_t v___y_507_; 
v___x_505_ = lean_array_get_size(v_x_497_);
if (lean_obj_tag(v_key_499_) == 0)
{
uint64_t v___x_525_; 
v___x_525_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_507_ = v___x_525_;
goto v___jp_506_;
}
else
{
uint64_t v_hash_526_; 
v_hash_526_ = lean_ctor_get_uint64(v_key_499_, sizeof(void*)*2);
v___y_507_ = v_hash_526_;
goto v___jp_506_;
}
v___jp_506_:
{
uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v_fold_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_508_ = 32ULL;
v___x_509_ = lean_uint64_shift_right(v___y_507_, v___x_508_);
v_fold_510_ = lean_uint64_xor(v___y_507_, v___x_509_);
v___x_511_ = 16ULL;
v___x_512_ = lean_uint64_shift_right(v_fold_510_, v___x_511_);
v___x_513_ = lean_uint64_xor(v_fold_510_, v___x_512_);
v___x_514_ = lean_uint64_to_usize(v___x_513_);
v___x_515_ = lean_usize_of_nat(v___x_505_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_sub(v___x_515_, v___x_516_);
v___x_518_ = lean_usize_land(v___x_514_, v___x_517_);
v___x_519_ = lean_array_uget_borrowed(v_x_497_, v___x_518_);
lean_inc(v___x_519_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 2, v___x_519_);
v___x_521_ = v___x_503_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_key_499_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_value_500_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v___x_519_);
v___x_521_ = v_reuseFailAlloc_524_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_array_uset(v_x_497_, v___x_518_, v___x_521_);
v_x_497_ = v___x_522_;
v_x_498_ = v_tail_501_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_528_, lean_object* v_source_529_, lean_object* v_target_530_){
_start:
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_array_get_size(v_source_529_);
v___x_532_ = lean_nat_dec_lt(v_i_528_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec_ref(v_source_529_);
lean_dec(v_i_528_);
return v_target_530_;
}
else
{
lean_object* v_es_533_; lean_object* v___x_534_; lean_object* v_source_535_; lean_object* v_target_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_es_533_ = lean_array_fget(v_source_529_, v_i_528_);
v___x_534_ = lean_box(0);
v_source_535_ = lean_array_fset(v_source_529_, v_i_528_, v___x_534_);
v_target_536_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_530_, v_es_533_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_i_528_, v___x_537_);
lean_dec(v_i_528_);
v_i_528_ = v___x_538_;
v_source_529_ = v_source_535_;
v_target_530_ = v_target_536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(lean_object* v_data_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_nbuckets_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_541_ = lean_array_get_size(v_data_540_);
v___x_542_ = lean_unsigned_to_nat(2u);
v_nbuckets_543_ = lean_nat_mul(v___x_541_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_box(0);
v___x_546_ = lean_mk_array(v_nbuckets_543_, v___x_545_);
v___x_547_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_544_, v_data_540_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
else
{
lean_object* v_key_551_; lean_object* v_tail_552_; uint8_t v___x_553_; 
v_key_551_ = lean_ctor_get(v_x_549_, 0);
v_tail_552_ = lean_ctor_get(v_x_549_, 2);
v___x_553_ = lean_name_eq(v_key_551_, v_a_548_);
if (v___x_553_ == 0)
{
v_x_549_ = v_tail_552_;
goto _start;
}
else
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_555_, v_x_556_);
lean_dec(v_x_556_);
lean_dec(v_a_555_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object* v_m_559_, lean_object* v_a_560_, lean_object* v_b_561_){
_start:
{
lean_object* v_size_562_; lean_object* v_buckets_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_609_; 
v_size_562_ = lean_ctor_get(v_m_559_, 0);
v_buckets_563_ = lean_ctor_get(v_m_559_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_m_559_);
if (v_isSharedCheck_609_ == 0)
{
v___x_565_ = v_m_559_;
v_isShared_566_ = v_isSharedCheck_609_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_buckets_563_);
lean_inc(v_size_562_);
lean_dec(v_m_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_609_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; uint64_t v___y_569_; 
v___x_567_ = lean_array_get_size(v_buckets_563_);
if (lean_obj_tag(v_a_560_) == 0)
{
uint64_t v___x_607_; 
v___x_607_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_569_ = v___x_607_;
goto v___jp_568_;
}
else
{
uint64_t v_hash_608_; 
v_hash_608_ = lean_ctor_get_uint64(v_a_560_, sizeof(void*)*2);
v___y_569_ = v_hash_608_;
goto v___jp_568_;
}
v___jp_568_:
{
uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v_fold_572_; uint64_t v___x_573_; uint64_t v___x_574_; uint64_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v_bkt_581_; uint8_t v___x_582_; 
v___x_570_ = 32ULL;
v___x_571_ = lean_uint64_shift_right(v___y_569_, v___x_570_);
v_fold_572_ = lean_uint64_xor(v___y_569_, v___x_571_);
v___x_573_ = 16ULL;
v___x_574_ = lean_uint64_shift_right(v_fold_572_, v___x_573_);
v___x_575_ = lean_uint64_xor(v_fold_572_, v___x_574_);
v___x_576_ = lean_uint64_to_usize(v___x_575_);
v___x_577_ = lean_usize_of_nat(v___x_567_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_sub(v___x_577_, v___x_578_);
v___x_580_ = lean_usize_land(v___x_576_, v___x_579_);
v_bkt_581_ = lean_array_uget_borrowed(v_buckets_563_, v___x_580_);
v___x_582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_560_, v_bkt_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v_size_x27_584_; lean_object* v___x_585_; lean_object* v_buckets_x27_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v_size_x27_584_ = lean_nat_add(v_size_562_, v___x_583_);
lean_dec(v_size_562_);
lean_inc(v_bkt_581_);
v___x_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_585_, 0, v_a_560_);
lean_ctor_set(v___x_585_, 1, v_b_561_);
lean_ctor_set(v___x_585_, 2, v_bkt_581_);
v_buckets_x27_586_ = lean_array_uset(v_buckets_563_, v___x_580_, v___x_585_);
v___x_587_ = lean_unsigned_to_nat(4u);
v___x_588_ = lean_nat_mul(v_size_x27_584_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(3u);
v___x_590_ = lean_nat_div(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_array_get_size(v_buckets_x27_586_);
v___x_592_ = lean_nat_dec_le(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
if (v___x_592_ == 0)
{
lean_object* v_val_593_; lean_object* v___x_595_; 
v_val_593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_586_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_val_593_);
lean_ctor_set(v___x_565_, 0, v_size_x27_584_);
v___x_595_ = v___x_565_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_size_x27_584_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_val_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_object* v___x_598_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_buckets_x27_586_);
lean_ctor_set(v___x_565_, 0, v_size_x27_584_);
v___x_598_ = v___x_565_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_size_x27_584_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_buckets_x27_586_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v___x_600_; lean_object* v_buckets_x27_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
lean_inc(v_bkt_581_);
v___x_600_ = lean_box(0);
v_buckets_x27_601_ = lean_array_uset(v_buckets_563_, v___x_580_, v___x_600_);
v___x_602_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_560_, v_b_561_, v_bkt_581_);
v___x_603_ = lean_array_uset(v_buckets_x27_601_, v___x_580_, v___x_602_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_603_);
v___x_605_ = v___x_565_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_size_562_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object* v_as_x27_610_, lean_object* v_b_611_){
_start:
{
if (lean_obj_tag(v_as_x27_610_) == 0)
{
return v_b_611_;
}
else
{
lean_object* v_head_612_; lean_object* v_tail_613_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v_r_616_; 
v_head_612_ = lean_ctor_get(v_as_x27_610_, 0);
lean_inc(v_head_612_);
v_tail_613_ = lean_ctor_get(v_as_x27_610_, 1);
lean_inc(v_tail_613_);
lean_dec_ref(v_as_x27_610_);
v_fst_614_ = lean_ctor_get(v_head_612_, 0);
lean_inc(v_fst_614_);
v_snd_615_ = lean_ctor_get(v_head_612_, 1);
lean_inc(v_snd_615_);
lean_dec(v_head_612_);
v_r_616_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_611_, v_fst_614_, v_snd_615_);
v_as_x27_610_ = v_tail_613_;
v_b_611_ = v_r_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* v_m_618_, lean_object* v_l_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_619_, v_m_618_);
return v___x_620_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_box(0);
v___x_684_ = lean_unsigned_to_nat(16u);
v___x_685_ = lean_mk_array(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
return v___x_688_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21));
v___x_691_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap(void){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_693_, lean_object* v_m_694_, lean_object* v_a_695_, lean_object* v_b_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_694_, v_a_695_, v_b_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object* v_as_698_, lean_object* v_as_x27_699_, lean_object* v_b_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_699_, v_b_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object* v_as_703_, lean_object* v_as_x27_704_, lean_object* v_b_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_703_, v_as_x27_704_, v_b_705_, v_a_706_);
lean_dec(v_as_703_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_708_, lean_object* v_a_709_, lean_object* v_x_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_712_, lean_object* v_a_713_, lean_object* v_x_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_712_, v_a_713_, v_x_714_);
lean_dec(v_x_714_);
lean_dec(v_a_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_717_, lean_object* v_data_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_720_, lean_object* v_a_721_, lean_object* v_b_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_721_, v_b_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_725_, lean_object* v_i_726_, lean_object* v_source_727_, lean_object* v_target_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_726_, v_source_727_, v_target_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object* v_name_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; lean_object* v_env_738_; lean_object* v___x_739_; lean_object* v_toEnvExtension_740_; lean_object* v_asyncMode_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_737_ = lean_st_ref_get(v___y_735_);
v_env_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc_ref(v_env_738_);
lean_dec(v___x_737_);
v___x_739_ = l_Lean_errorExplanationExt;
v_toEnvExtension_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_toEnvExtension_740_);
v_asyncMode_741_ = lean_ctor_get(v_toEnvExtension_740_, 2);
lean_inc(v_asyncMode_741_);
lean_dec_ref(v_toEnvExtension_740_);
v___x_742_ = lean_box(1);
v___x_743_ = lean_box(0);
v___x_744_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_742_, v___x_739_, v_env_738_, v_asyncMode_741_, v___x_743_);
lean_dec(v_asyncMode_741_);
v___x_745_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_744_, v_name_734_);
lean_dec(v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object* v_name_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec(v_name_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object* v_name_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_751_, v___y_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object* v_name_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v_name_760_);
return v_res_768_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_box(0);
v___x_770_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg(){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___boxed(lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg();
return v_res_776_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_box(1);
v___x_778_ = l_Lean_MessageData_ofFormat(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__2));
v___x_783_ = l_Lean_MessageData_ofFormat(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
return v_x_784_;
}
else
{
lean_object* v_head_786_; lean_object* v_tail_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_809_; 
v_head_786_ = lean_ctor_get(v_x_785_, 0);
v_tail_787_ = lean_ctor_get(v_x_785_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_809_ == 0)
{
v___x_789_ = v_x_785_;
v_isShared_790_ = v_isSharedCheck_809_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_tail_787_);
lean_inc(v_head_786_);
lean_dec(v_x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_809_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_before_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_807_; 
v_before_791_ = lean_ctor_get(v_head_786_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_head_786_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_head_786_, 1);
lean_dec(v_unused_808_);
v___x_793_ = v_head_786_;
v_isShared_794_ = v_isSharedCheck_807_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_before_791_);
lean_dec(v_head_786_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_807_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 7);
lean_ctor_set(v___x_793_, 1, v___x_795_);
lean_ctor_set(v___x_793_, 0, v_x_784_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_x_784_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_806_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__3);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 7);
lean_ctor_set(v___x_789_, 1, v___x_798_);
lean_ctor_set(v___x_789_, 0, v___x_797_);
v___x_800_ = v___x_789_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_805_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = l_Lean_MessageData_ofSyntax(v_before_791_);
v___x_802_ = l_Lean_indentD(v___x_801_);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v_x_784_ = v___x_803_;
v_x_785_ = v_tail_787_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17(lean_object* v_opts_810_, lean_object* v_opt_811_){
_start:
{
lean_object* v_name_812_; lean_object* v_defValue_813_; lean_object* v_map_814_; lean_object* v___x_815_; 
v_name_812_ = lean_ctor_get(v_opt_811_, 0);
v_defValue_813_ = lean_ctor_get(v_opt_811_, 1);
v_map_814_ = lean_ctor_get(v_opts_810_, 0);
v___x_815_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_814_, v_name_812_);
if (lean_obj_tag(v___x_815_) == 0)
{
uint8_t v___x_816_; 
v___x_816_ = lean_unbox(v_defValue_813_);
return v___x_816_;
}
else
{
lean_object* v_val_817_; 
v_val_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_817_);
lean_dec_ref(v___x_815_);
if (lean_obj_tag(v_val_817_) == 1)
{
uint8_t v_v_818_; 
v_v_818_ = lean_ctor_get_uint8(v_val_817_, 0);
lean_dec_ref(v_val_817_);
return v_v_818_;
}
else
{
uint8_t v___x_819_; 
lean_dec(v_val_817_);
v___x_819_ = lean_unbox(v_defValue_813_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17___boxed(lean_object* v_opts_820_, lean_object* v_opt_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17(v_opts_820_, v_opt_821_);
lean_dec_ref(v_opt_821_);
lean_dec_ref(v_opts_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__1));
v___x_828_ = l_Lean_MessageData_ofFormat(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg(lean_object* v_msgData_829_, lean_object* v_macroStack_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_options_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_options_833_ = lean_ctor_get(v___y_831_, 2);
v___x_834_ = l_Lean_Elab_pp_macroStack;
v___x_835_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17(v_options_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v_macroStack_830_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_msgData_829_);
return v___x_836_;
}
else
{
if (lean_obj_tag(v_macroStack_830_) == 0)
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v_msgData_829_);
return v___x_837_;
}
else
{
lean_object* v_head_838_; lean_object* v_after_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_854_; 
v_head_838_ = lean_ctor_get(v_macroStack_830_, 0);
lean_inc(v_head_838_);
v_after_839_ = lean_ctor_get(v_head_838_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_head_838_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_head_838_, 0);
lean_dec(v_unused_855_);
v___x_841_ = v_head_838_;
v_isShared_842_ = v_isSharedCheck_854_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_after_839_);
lean_dec(v_head_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_854_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 7);
lean_ctor_set(v___x_841_, 1, v___x_843_);
lean_ctor_set(v___x_841_, 0, v_msgData_829_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_msgData_829_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_853_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_msgData_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_846_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_MessageData_ofSyntax(v_after_839_);
v___x_849_ = l_Lean_indentD(v___x_848_);
v_msgData_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_850_, 0, v___x_847_);
lean_ctor_set(v_msgData_850_, 1, v___x_849_);
v___x_851_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24(v_msgData_850_, v_macroStack_830_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___boxed(lean_object* v_msgData_856_, lean_object* v_macroStack_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg(v_msgData_856_, v_macroStack_857_, v___y_858_);
lean_dec_ref(v___y_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object* v_msgData_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_env_868_; lean_object* v___x_869_; lean_object* v_mctx_870_; lean_object* v_lctx_871_; lean_object* v_options_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_867_ = lean_st_ref_get(v___y_865_);
v_env_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_env_868_);
lean_dec(v___x_867_);
v___x_869_ = lean_st_ref_get(v___y_863_);
v_mctx_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_mctx_870_);
lean_dec(v___x_869_);
v_lctx_871_ = lean_ctor_get(v___y_862_, 2);
v_options_872_ = lean_ctor_get(v___y_864_, 2);
lean_inc_ref(v_options_872_);
lean_inc_ref(v_lctx_871_);
v___x_873_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_873_, 0, v_env_868_);
lean_ctor_set(v___x_873_, 1, v_mctx_870_);
lean_ctor_set(v___x_873_, 2, v_lctx_871_);
lean_ctor_set(v___x_873_, 3, v_options_872_);
v___x_874_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v_msgData_861_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object* v_msgData_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v_macroStack_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_ref_891_ = lean_ctor_get(v___y_888_, 5);
v___x_892_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msg_883_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_892_);
v_macroStack_894_ = lean_ctor_get(v___y_884_, 1);
lean_inc(v_macroStack_894_);
lean_dec_ref(v___y_884_);
lean_inc(v_macroStack_894_);
v___x_895_ = l_Lean_Elab_getBetterRef(v_ref_891_, v_macroStack_894_);
v___x_896_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg(v_a_893_, v_macroStack_894_, v___y_888_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_895_);
lean_ctor_set(v___x_901_, 1, v_a_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 1);
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object* v_ref_915_, lean_object* v_msg_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_fileName_924_; lean_object* v_fileMap_925_; lean_object* v_options_926_; lean_object* v_currRecDepth_927_; lean_object* v_maxRecDepth_928_; lean_object* v_ref_929_; lean_object* v_currNamespace_930_; lean_object* v_openDecls_931_; lean_object* v_initHeartbeats_932_; lean_object* v_maxHeartbeats_933_; lean_object* v_quotContext_934_; lean_object* v_currMacroScope_935_; uint8_t v_diag_936_; lean_object* v_cancelTk_x3f_937_; uint8_t v_suppressElabErrors_938_; lean_object* v_inheritedTraceOptions_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v_fileName_924_ = lean_ctor_get(v___y_921_, 0);
v_fileMap_925_ = lean_ctor_get(v___y_921_, 1);
v_options_926_ = lean_ctor_get(v___y_921_, 2);
v_currRecDepth_927_ = lean_ctor_get(v___y_921_, 3);
v_maxRecDepth_928_ = lean_ctor_get(v___y_921_, 4);
v_ref_929_ = lean_ctor_get(v___y_921_, 5);
v_currNamespace_930_ = lean_ctor_get(v___y_921_, 6);
v_openDecls_931_ = lean_ctor_get(v___y_921_, 7);
v_initHeartbeats_932_ = lean_ctor_get(v___y_921_, 8);
v_maxHeartbeats_933_ = lean_ctor_get(v___y_921_, 9);
v_quotContext_934_ = lean_ctor_get(v___y_921_, 10);
v_currMacroScope_935_ = lean_ctor_get(v___y_921_, 11);
v_diag_936_ = lean_ctor_get_uint8(v___y_921_, sizeof(void*)*14);
v_cancelTk_x3f_937_ = lean_ctor_get(v___y_921_, 12);
v_suppressElabErrors_938_ = lean_ctor_get_uint8(v___y_921_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_939_ = lean_ctor_get(v___y_921_, 13);
v_isSharedCheck_948_ = !lean_is_exclusive(v___y_921_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v___y_921_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_inheritedTraceOptions_939_);
lean_inc(v_cancelTk_x3f_937_);
lean_inc(v_currMacroScope_935_);
lean_inc(v_quotContext_934_);
lean_inc(v_maxHeartbeats_933_);
lean_inc(v_initHeartbeats_932_);
lean_inc(v_openDecls_931_);
lean_inc(v_currNamespace_930_);
lean_inc(v_ref_929_);
lean_inc(v_maxRecDepth_928_);
lean_inc(v_currRecDepth_927_);
lean_inc(v_options_926_);
lean_inc(v_fileMap_925_);
lean_inc(v_fileName_924_);
lean_dec(v___y_921_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_ref_943_; lean_object* v___x_945_; 
v_ref_943_ = l_Lean_replaceRef(v_ref_915_, v_ref_929_);
lean_dec(v_ref_929_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 5, v_ref_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fileName_924_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_fileMap_925_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_options_926_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_currRecDepth_927_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_maxRecDepth_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v_ref_943_);
lean_ctor_set(v_reuseFailAlloc_947_, 6, v_currNamespace_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 7, v_openDecls_931_);
lean_ctor_set(v_reuseFailAlloc_947_, 8, v_initHeartbeats_932_);
lean_ctor_set(v_reuseFailAlloc_947_, 9, v_maxHeartbeats_933_);
lean_ctor_set(v_reuseFailAlloc_947_, 10, v_quotContext_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 11, v_currMacroScope_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 12, v_cancelTk_x3f_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 13, v_inheritedTraceOptions_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*14, v_diag_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*14 + 1, v_suppressElabErrors_938_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___x_945_, v___y_922_);
lean_dec_ref(v___x_945_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object* v_ref_949_, lean_object* v_msg_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_949_, v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v_ref_949_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = l_Lean_maxRecDepthErrorMessage;
v___x_965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__3);
v___x_967_ = l_Lean_MessageData_ofFormat(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__4);
v___x_969_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__2));
v___x_970_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(lean_object* v_ref_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__5);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_ref_971_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object* v_ref_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(v_ref_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object* v_env_979_, lean_object* v_declName_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_983_; lean_object* v_env_984_; lean_object* v___x_985_; uint8_t v___x_986_; uint8_t v___x_987_; 
v___x_983_ = 0;
v_env_984_ = l_Lean_Environment_setExporting(v_env_979_, v___x_983_);
lean_inc(v_declName_980_);
v___x_985_ = l_Lean_mkPrivateName(v_env_984_, v_declName_980_);
v___x_986_ = 1;
lean_inc_ref(v_env_984_);
v___x_987_ = l_Lean_Environment_contains(v_env_984_, v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = l_Lean_privateToUserName(v_declName_980_);
v___x_989_ = l_Lean_Environment_contains(v_env_984_, v___x_988_, v___x_986_);
v___x_990_ = lean_box(v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___y_982_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v_env_984_);
lean_dec(v_declName_980_);
v___x_992_ = lean_box(v___x_987_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___y_982_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object* v_env_994_, lean_object* v_declName_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_994_, v_declName_995_, v___y_996_, v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg(lean_object* v_x_999_, lean_object* v___y_1000_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_a_1001_);
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_1001_);
lean_ctor_set(v___x_1002_, 1, v___y_1000_);
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_a_1003_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_a_1003_);
lean_ctor_set(v___x_1004_, 1, v___y_1000_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg___boxed(lean_object* v_x_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg(v_x_1005_, v___y_1006_);
lean_dec_ref(v_x_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object* v_env_1008_, lean_object* v_stx_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1008_, v_stx_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_a_1014_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1023_);
v___x_1016_ = v___x_1012_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_a_1014_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1052_; 
v_val_1024_ = lean_ctor_get(v_a_1013_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1026_ = v_a_1013_;
v_isShared_1027_ = v_isSharedCheck_1052_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_val_1024_);
lean_dec(v_a_1013_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1052_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_snd_1028_; 
v_snd_1028_ = lean_ctor_get(v_val_1024_, 1);
lean_inc(v_snd_1028_);
lean_dec(v_val_1024_);
if (lean_obj_tag(v_snd_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_1026_);
v_a_1029_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1012_);
v_a_1030_ = lean_ctor_get(v_snd_1028_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_snd_1028_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v_snd_1028_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v_snd_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg(v___x_1035_, v_a_1029_);
lean_dec_ref(v___x_1035_);
return v___x_1036_;
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1051_; 
v_a_1039_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1012_);
v_a_1040_ = lean_ctor_get(v_snd_1028_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_snd_1028_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1042_ = v_snd_1028_;
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v_snd_1028_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v_a_1040_);
v___x_1045_ = v___x_1026_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1045_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg(v___x_1047_, v_a_1039_);
lean_dec_ref(v___x_1047_);
return v___x_1048_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v___x_1012_, 0);
v_a_1054_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1012_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_1012_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_a_1054_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object* v_env_1062_, lean_object* v_stx_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_1062_, v_stx_1063_, v___y_1064_, v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object* v_cls_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_options_1073_; uint8_t v_hasTrace_1074_; 
v_options_1073_ = lean_ctor_get(v___y_1071_, 2);
v_hasTrace_1074_ = lean_ctor_get_uint8(v_options_1073_, sizeof(void*)*1);
if (v_hasTrace_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_cls_1070_);
v___x_1075_ = lean_box(v_hasTrace_1074_);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_inheritedTraceOptions_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_inheritedTraceOptions_1077_ = lean_ctor_get(v___y_1071_, 13);
v___x_1078_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1079_ = l_Lean_Name_append(v___x_1078_, v_cls_1070_);
v___x_1080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1077_, v_options_1073_, v___x_1079_);
lean_dec(v___x_1079_);
v___x_1081_ = lean_box(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object* v_cls_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1083_, v___y_1084_);
lean_dec_ref(v___y_1084_);
return v_res_1086_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1087_; double v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_float_of_nat(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object* v_cls_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_ref_1099_; lean_object* v___x_1100_; lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1145_; 
v_ref_1099_ = lean_ctor_get(v___y_1096_, 5);
v___x_1100_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1145_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1145_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v_traceState_1106_; lean_object* v_env_1107_; lean_object* v_nextMacroScope_1108_; lean_object* v_ngen_1109_; lean_object* v_auxDeclNGen_1110_; lean_object* v_cache_1111_; lean_object* v_messages_1112_; lean_object* v_infoState_1113_; lean_object* v_snapshotTasks_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1144_; 
v___x_1105_ = lean_st_ref_take(v___y_1097_);
v_traceState_1106_ = lean_ctor_get(v___x_1105_, 4);
v_env_1107_ = lean_ctor_get(v___x_1105_, 0);
v_nextMacroScope_1108_ = lean_ctor_get(v___x_1105_, 1);
v_ngen_1109_ = lean_ctor_get(v___x_1105_, 2);
v_auxDeclNGen_1110_ = lean_ctor_get(v___x_1105_, 3);
v_cache_1111_ = lean_ctor_get(v___x_1105_, 5);
v_messages_1112_ = lean_ctor_get(v___x_1105_, 6);
v_infoState_1113_ = lean_ctor_get(v___x_1105_, 7);
v_snapshotTasks_1114_ = lean_ctor_get(v___x_1105_, 8);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1116_ = v___x_1105_;
v_isShared_1117_ = v_isSharedCheck_1144_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_snapshotTasks_1114_);
lean_inc(v_infoState_1113_);
lean_inc(v_messages_1112_);
lean_inc(v_cache_1111_);
lean_inc(v_traceState_1106_);
lean_inc(v_auxDeclNGen_1110_);
lean_inc(v_ngen_1109_);
lean_inc(v_nextMacroScope_1108_);
lean_inc(v_env_1107_);
lean_dec(v___x_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1144_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
uint64_t v_tid_1118_; lean_object* v_traces_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1143_; 
v_tid_1118_ = lean_ctor_get_uint64(v_traceState_1106_, sizeof(void*)*1);
v_traces_1119_ = lean_ctor_get(v_traceState_1106_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_traceState_1106_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1121_ = v_traceState_1106_;
v_isShared_1122_ = v_isSharedCheck_1143_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_traces_1119_);
lean_dec(v_traceState_1106_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1143_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; double v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0);
v___x_1125_ = 0;
v___x_1126_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1));
v___x_1127_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1127_, 0, v_cls_1092_);
lean_ctor_set(v___x_1127_, 1, v___x_1123_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
lean_ctor_set_float(v___x_1127_, sizeof(void*)*3, v___x_1124_);
lean_ctor_set_float(v___x_1127_, sizeof(void*)*3 + 8, v___x_1124_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*3 + 16, v___x_1125_);
v___x_1128_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__2));
v___x_1129_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v_a_1101_);
lean_ctor_set(v___x_1129_, 2, v___x_1128_);
lean_inc(v_ref_1099_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_ref_1099_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_PersistentArray_push___redArg(v_traces_1119_, v___x_1130_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1131_);
v___x_1133_ = v___x_1121_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1131_);
lean_ctor_set_uint64(v_reuseFailAlloc_1142_, sizeof(void*)*1, v_tid_1118_);
v___x_1133_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v___x_1133_);
v___x_1135_ = v___x_1116_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_env_1107_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_nextMacroScope_1108_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_ngen_1109_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_auxDeclNGen_1110_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_cache_1111_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v_messages_1112_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_infoState_1113_);
lean_ctor_set(v_reuseFailAlloc_1141_, 8, v_snapshotTasks_1114_);
v___x_1135_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = lean_st_ref_set(v___y_1097_, v___x_1135_);
v___x_1137_ = lean_box(0);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1137_);
v___x_1139_ = v___x_1103_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object* v_cls_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_cls_1146_, v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object* v_as_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
if (lean_obj_tag(v_as_1154_) == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
else
{
lean_object* v_head_1164_; lean_object* v_tail_1165_; lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1168_; lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1181_; 
v_head_1164_ = lean_ctor_get(v_as_1154_, 0);
lean_inc(v_head_1164_);
v_tail_1165_ = lean_ctor_get(v_as_1154_, 1);
lean_inc(v_tail_1165_);
lean_dec_ref(v_as_1154_);
v_fst_1166_ = lean_ctor_get(v_head_1164_, 0);
lean_inc(v_fst_1166_);
v_snd_1167_ = lean_ctor_get(v_head_1164_, 1);
lean_inc(v_snd_1167_);
lean_dec(v_head_1164_);
lean_inc(v_fst_1166_);
v___x_1168_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_1166_, v___y_1159_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
if (v___x_1173_ == 0)
{
lean_del_object(v___x_1171_);
lean_dec(v_snd_1167_);
lean_dec(v_fst_1166_);
v_as_1154_ = v_tail_1165_;
goto _start;
}
else
{
lean_object* v___x_1176_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 3);
lean_ctor_set(v___x_1171_, 0, v_snd_1167_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_snd_1167_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_MessageData_ofFormat(v___x_1176_);
v___x_1178_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_fst_1166_, v___x_1177_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_dec_ref(v___x_1178_);
v_as_1154_ = v_tail_1165_;
goto _start;
}
else
{
lean_dec(v_tail_1165_);
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object* v_as_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_as_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object* v_env_1191_, lean_object* v_options_1192_, lean_object* v_currNamespace_1193_, lean_object* v_openDecls_1194_, lean_object* v_n_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = l_Lean_ResolveName_resolveGlobalName(v_env_1191_, v_options_1192_, v_currNamespace_1193_, v_openDecls_1194_, v_n_1195_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___y_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object* v_env_1200_, lean_object* v_options_1201_, lean_object* v_currNamespace_1202_, lean_object* v_openDecls_1203_, lean_object* v_n_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_1200_, v_options_1201_, v_currNamespace_1202_, v_openDecls_1203_, v_n_1204_, v___y_1205_, v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_options_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object* v_currNamespace_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_currNamespace_1208_);
lean_ctor_set(v___x_1211_, 1, v___y_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_1212_, v___y_1213_, v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg(lean_object* v_a_1216_, lean_object* v_x_1217_){
_start:
{
if (lean_obj_tag(v_x_1217_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_box(0);
return v___x_1218_;
}
else
{
lean_object* v_key_1219_; lean_object* v_value_1220_; lean_object* v_tail_1221_; uint8_t v___x_1222_; 
v_key_1219_ = lean_ctor_get(v_x_1217_, 0);
v_value_1220_ = lean_ctor_get(v_x_1217_, 1);
v_tail_1221_ = lean_ctor_get(v_x_1217_, 2);
v___x_1222_ = lean_name_eq(v_key_1219_, v_a_1216_);
if (v___x_1222_ == 0)
{
v_x_1217_ = v_tail_1221_;
goto _start;
}
else
{
lean_object* v___x_1224_; 
lean_inc(v_value_1220_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_value_1220_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg___boxed(lean_object* v_a_1225_, lean_object* v_x_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg(v_a_1225_, v_x_1226_);
lean_dec(v_x_1226_);
lean_dec(v_a_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object* v_m_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_buckets_1230_; lean_object* v___x_1231_; uint64_t v___y_1233_; 
v_buckets_1230_ = lean_ctor_get(v_m_1228_, 1);
v___x_1231_ = lean_array_get_size(v_buckets_1230_);
if (lean_obj_tag(v_a_1229_) == 0)
{
uint64_t v___x_1247_; 
v___x_1247_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_1233_ = v___x_1247_;
goto v___jp_1232_;
}
else
{
uint64_t v_hash_1248_; 
v_hash_1248_ = lean_ctor_get_uint64(v_a_1229_, sizeof(void*)*2);
v___y_1233_ = v_hash_1248_;
goto v___jp_1232_;
}
v___jp_1232_:
{
uint64_t v___x_1234_; uint64_t v___x_1235_; uint64_t v_fold_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; uint64_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1234_ = 32ULL;
v___x_1235_ = lean_uint64_shift_right(v___y_1233_, v___x_1234_);
v_fold_1236_ = lean_uint64_xor(v___y_1233_, v___x_1235_);
v___x_1237_ = 16ULL;
v___x_1238_ = lean_uint64_shift_right(v_fold_1236_, v___x_1237_);
v___x_1239_ = lean_uint64_xor(v_fold_1236_, v___x_1238_);
v___x_1240_ = lean_uint64_to_usize(v___x_1239_);
v___x_1241_ = lean_usize_of_nat(v___x_1231_);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_sub(v___x_1241_, v___x_1242_);
v___x_1244_ = lean_usize_land(v___x_1240_, v___x_1243_);
v___x_1245_ = lean_array_uget_borrowed(v_buckets_1230_, v___x_1244_);
v___x_1246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg(v_a_1229_, v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object* v_m_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_m_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg(lean_object* v_keys_1252_, lean_object* v_i_1253_, lean_object* v_k_1254_){
_start:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_array_get_size(v_keys_1252_);
v___x_1256_ = lean_nat_dec_lt(v_i_1253_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v_i_1253_);
return v___x_1256_;
}
else
{
lean_object* v_k_x27_1257_; uint8_t v___x_1258_; 
v_k_x27_1257_ = lean_array_fget_borrowed(v_keys_1252_, v_i_1253_);
v___x_1258_ = l_Lean_instBEqExtraModUse_beq(v_k_1254_, v_k_x27_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_add(v_i_1253_, v___x_1259_);
lean_dec(v_i_1253_);
v_i_1253_ = v___x_1260_;
goto _start;
}
else
{
lean_dec(v_i_1253_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg___boxed(lean_object* v_keys_1262_, lean_object* v_i_1263_, lean_object* v_k_1264_){
_start:
{
uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_res_1265_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg(v_keys_1262_, v_i_1263_, v_k_1264_);
lean_dec_ref(v_k_1264_);
lean_dec_ref(v_keys_1262_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__0(void){
_start:
{
size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; 
v___x_1267_ = ((size_t)5ULL);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_shift_left(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__1(void){
_start:
{
size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; 
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__0);
v___x_1272_ = lean_usize_sub(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg(lean_object* v_x_1273_, size_t v_x_1274_, lean_object* v_x_1275_){
_start:
{
if (lean_obj_tag(v_x_1273_) == 0)
{
lean_object* v_es_1276_; lean_object* v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; lean_object* v_j_1281_; lean_object* v___x_1282_; 
v_es_1276_ = lean_ctor_get(v_x_1273_, 0);
lean_inc_ref(v_es_1276_);
lean_dec_ref(v_x_1273_);
v___x_1277_ = lean_box(2);
v___x_1278_ = ((size_t)5ULL);
v___x_1279_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___closed__1);
v___x_1280_ = lean_usize_land(v_x_1274_, v___x_1279_);
v_j_1281_ = lean_usize_to_nat(v___x_1280_);
v___x_1282_ = lean_array_get(v___x_1277_, v_es_1276_, v_j_1281_);
lean_dec(v_j_1281_);
lean_dec_ref(v_es_1276_);
switch(lean_obj_tag(v___x_1282_))
{
case 0:
{
lean_object* v_key_1283_; uint8_t v___x_1284_; 
v_key_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_key_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = l_Lean_instBEqExtraModUse_beq(v_x_1275_, v_key_1283_);
lean_dec(v_key_1283_);
return v___x_1284_;
}
case 1:
{
lean_object* v_node_1285_; size_t v___x_1286_; 
v_node_1285_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_node_1285_);
lean_dec_ref(v___x_1282_);
v___x_1286_ = lean_usize_shift_right(v_x_1274_, v___x_1278_);
v_x_1273_ = v_node_1285_;
v_x_1274_ = v___x_1286_;
goto _start;
}
default: 
{
uint8_t v___x_1288_; 
v___x_1288_ = 0;
return v___x_1288_;
}
}
}
else
{
lean_object* v_ks_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_ks_1289_ = lean_ctor_get(v_x_1273_, 0);
lean_inc_ref(v_ks_1289_);
lean_dec_ref(v_x_1273_);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg(v_ks_1289_, v___x_1290_, v_x_1275_);
lean_dec_ref(v_ks_1289_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg___boxed(lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
size_t v_x_20418__boxed_1295_; uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_x_20418__boxed_1295_ = lean_unbox_usize(v_x_1293_);
lean_dec(v_x_1293_);
v_res_1296_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg(v_x_1292_, v_x_20418__boxed_1295_, v_x_1294_);
lean_dec_ref(v_x_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg(lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
uint64_t v___x_1300_; size_t v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = l_Lean_instHashableExtraModUse_hash(v_x_1299_);
v___x_1301_ = lean_uint64_to_usize(v___x_1300_);
v___x_1302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg(v_x_1298_, v___x_1301_, v_x_1299_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg___boxed(lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg(v_x_1303_, v_x_1304_);
lean_dec_ref(v_x_1304_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__1));
v___x_1310_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__0));
v___x_1311_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__3);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__4);
v___x_1318_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_ctor_set(v___x_1318_, 2, v___x_1317_);
lean_ctor_set(v___x_1318_, 3, v___x_1317_);
lean_ctor_set(v___x_1318_, 4, v___x_1317_);
lean_ctor_set(v___x_1318_, 5, v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__9));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__11));
v___x_1327_ = l_Lean_stringToMessageData(v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__14));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__16));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5(lean_object* v_mod_1340_, uint8_t v_isMeta_1341_, lean_object* v_hint_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v_env_1351_; uint8_t v_isExporting_1352_; lean_object* v___x_1353_; lean_object* v_env_1354_; lean_object* v___x_1355_; lean_object* v_entry_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1350_ = lean_st_ref_get(v___y_1348_);
v_env_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_ref(v_env_1351_);
lean_dec(v___x_1350_);
v_isExporting_1352_ = lean_ctor_get_uint8(v_env_1351_, sizeof(void*)*8);
lean_dec_ref(v_env_1351_);
v___x_1353_ = lean_st_ref_get(v___y_1348_);
v_env_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_env_1354_);
lean_dec(v___x_1353_);
v___x_1355_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2);
lean_inc(v_mod_1340_);
v_entry_1356_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1356_, 0, v_mod_1340_);
lean_ctor_set_uint8(v_entry_1356_, sizeof(void*)*1, v_isExporting_1352_);
lean_ctor_set_uint8(v_entry_1356_, sizeof(void*)*1 + 1, v_isMeta_1341_);
v___x_1357_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1358_ = lean_box(1);
v___x_1359_ = lean_box(0);
v___x_1402_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1355_, v___x_1357_, v_env_1354_, v___x_1358_, v___x_1359_);
v___x_1403_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg(v___x_1402_, v_entry_1356_);
if (v___x_1403_ == 0)
{
lean_object* v_cls_1404_; lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1413_; lean_object* v___y_1414_; uint8_t v___x_1426_; 
v_cls_1404_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__8));
v___x_1405_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1404_, v___y_1347_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref(v___x_1405_);
v___x_1426_ = lean_unbox(v_a_1406_);
lean_dec(v_a_1406_);
if (v___x_1426_ == 0)
{
lean_dec(v_hint_1342_);
lean_dec(v_mod_1340_);
v___y_1361_ = v___y_1346_;
v___y_1362_ = v___y_1348_;
goto v___jp_1360_;
}
else
{
lean_object* v___x_1427_; lean_object* v___y_1429_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15);
if (v_isExporting_1352_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__20));
v___y_1429_ = v___x_1436_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1437_; 
v___x_1437_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__21));
v___y_1429_ = v___x_1437_;
goto v___jp_1428_;
}
v___jp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1430_ = l_Lean_stringToMessageData(v___y_1429_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1427_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
if (v_isMeta_1341_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__18));
v___y_1413_ = v___x_1433_;
v___y_1414_ = v___x_1434_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__19));
v___y_1413_ = v___x_1433_;
v___y_1414_ = v___x_1435_;
goto v___jp_1412_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1408_);
lean_ctor_set(v___x_1410_, 1, v___y_1409_);
v___x_1411_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_cls_1404_, v___x_1410_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref(v___x_1411_);
v___y_1361_ = v___y_1346_;
v___y_1362_ = v___y_1348_;
goto v___jp_1360_;
}
else
{
lean_dec_ref(v_entry_1356_);
return v___x_1411_;
}
}
v___jp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1415_ = l_Lean_stringToMessageData(v___y_1414_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1413_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_MessageData_ofName(v_mod_1340_);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Lean_Name_isAnonymous(v_hint_1342_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12);
v___x_1423_ = l_Lean_MessageData_ofName(v_hint_1342_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___y_1408_ = v___x_1420_;
v___y_1409_ = v___x_1424_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_hint_1342_);
v___x_1425_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13);
v___y_1408_ = v___x_1420_;
v___y_1409_ = v___x_1425_;
goto v___jp_1407_;
}
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_entry_1356_);
lean_dec(v_hint_1342_);
lean_dec(v_mod_1340_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
v___jp_1360_:
{
lean_object* v___x_1363_; lean_object* v_toEnvExtension_1364_; lean_object* v_env_1365_; lean_object* v_nextMacroScope_1366_; lean_object* v_ngen_1367_; lean_object* v_auxDeclNGen_1368_; lean_object* v_traceState_1369_; lean_object* v_messages_1370_; lean_object* v_infoState_1371_; lean_object* v_snapshotTasks_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1400_; 
v___x_1363_ = lean_st_ref_take(v___y_1362_);
v_toEnvExtension_1364_ = lean_ctor_get(v___x_1357_, 0);
lean_inc_ref(v_toEnvExtension_1364_);
v_env_1365_ = lean_ctor_get(v___x_1363_, 0);
v_nextMacroScope_1366_ = lean_ctor_get(v___x_1363_, 1);
v_ngen_1367_ = lean_ctor_get(v___x_1363_, 2);
v_auxDeclNGen_1368_ = lean_ctor_get(v___x_1363_, 3);
v_traceState_1369_ = lean_ctor_get(v___x_1363_, 4);
v_messages_1370_ = lean_ctor_get(v___x_1363_, 6);
v_infoState_1371_ = lean_ctor_get(v___x_1363_, 7);
v_snapshotTasks_1372_ = lean_ctor_get(v___x_1363_, 8);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1363_, 5);
lean_dec(v_unused_1401_);
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1400_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snapshotTasks_1372_);
lean_inc(v_infoState_1371_);
lean_inc(v_messages_1370_);
lean_inc(v_traceState_1369_);
lean_inc(v_auxDeclNGen_1368_);
lean_inc(v_ngen_1367_);
lean_inc(v_nextMacroScope_1366_);
lean_inc(v_env_1365_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1400_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v_asyncMode_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v_asyncMode_1376_ = lean_ctor_get(v_toEnvExtension_1364_, 2);
lean_inc(v_asyncMode_1376_);
lean_dec_ref(v_toEnvExtension_1364_);
v___x_1377_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1357_, v_env_1365_, v_entry_1356_, v_asyncMode_1376_, v___x_1359_);
lean_dec(v_asyncMode_1376_);
v___x_1378_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__5);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 5, v___x_1378_);
lean_ctor_set(v___x_1374_, 0, v___x_1377_);
v___x_1380_ = v___x_1374_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_nextMacroScope_1366_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_ngen_1367_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_auxDeclNGen_1368_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_traceState_1369_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_messages_1370_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_infoState_1371_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_snapshotTasks_1372_);
v___x_1380_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_mctx_1383_; lean_object* v_zetaDeltaFVarIds_1384_; lean_object* v_postponed_1385_; lean_object* v_diag_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1397_; 
v___x_1381_ = lean_st_ref_set(v___y_1362_, v___x_1380_);
v___x_1382_ = lean_st_ref_take(v___y_1361_);
v_mctx_1383_ = lean_ctor_get(v___x_1382_, 0);
v_zetaDeltaFVarIds_1384_ = lean_ctor_get(v___x_1382_, 2);
v_postponed_1385_ = lean_ctor_get(v___x_1382_, 3);
v_diag_1386_ = lean_ctor_get(v___x_1382_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1382_, 1);
lean_dec(v_unused_1398_);
v___x_1388_ = v___x_1382_;
v_isShared_1389_ = v_isSharedCheck_1397_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_diag_1386_);
lean_inc(v_postponed_1385_);
lean_inc(v_zetaDeltaFVarIds_1384_);
lean_inc(v_mctx_1383_);
lean_dec(v___x_1382_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1397_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__6);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v___x_1390_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_mctx_1383_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_zetaDeltaFVarIds_1384_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_postponed_1385_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_diag_1386_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_st_ref_set(v___y_1361_, v___x_1392_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___boxed(lean_object* v_mod_1440_, lean_object* v_isMeta_1441_, lean_object* v_hint_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_isMeta_boxed_1450_; lean_object* v_res_1451_; 
v_isMeta_boxed_1450_ = lean_unbox(v_isMeta_1441_);
v_res_1451_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5(v_mod_1440_, v_isMeta_boxed_1450_, v_hint_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__6(lean_object* v___x_1452_, lean_object* v_declName_1453_, lean_object* v_as_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_dec(v_declName_1453_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_b_1457_);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; lean_object* v_modules_1468_; lean_object* v___x_1469_; lean_object* v_a_1470_; lean_object* v___x_1471_; lean_object* v_toImport_1472_; lean_object* v_module_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1467_ = l_Lean_Environment_header(v___x_1452_);
v_modules_1468_ = lean_ctor_get(v___x_1467_, 3);
lean_inc_ref(v_modules_1468_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1470_ = lean_array_uget_borrowed(v_as_1454_, v_i_1456_);
v___x_1471_ = lean_array_get(v___x_1469_, v_modules_1468_, v_a_1470_);
lean_dec_ref(v_modules_1468_);
v_toImport_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc_ref(v_toImport_1472_);
lean_dec(v___x_1471_);
v_module_1473_ = lean_ctor_get(v_toImport_1472_, 0);
lean_inc(v_module_1473_);
lean_dec_ref(v_toImport_1472_);
v___x_1474_ = 0;
lean_inc(v_declName_1453_);
v___x_1475_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5(v_module_1473_, v___x_1474_, v_declName_1453_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; 
lean_dec_ref(v___x_1475_);
v___x_1476_ = lean_box(0);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_add(v_i_1456_, v___x_1477_);
v_i_1456_ = v___x_1478_;
v_b_1457_ = v___x_1476_;
goto _start;
}
else
{
lean_dec(v_declName_1453_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__6___boxed(lean_object* v___x_1480_, lean_object* v_declName_1481_, lean_object* v_as_1482_, lean_object* v_sz_1483_, lean_object* v_i_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
size_t v_sz_boxed_1493_; size_t v_i_boxed_1494_; lean_object* v_res_1495_; 
v_sz_boxed_1493_ = lean_unbox_usize(v_sz_1483_);
lean_dec(v_sz_1483_);
v_i_boxed_1494_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__6(v___x_1480_, v_declName_1481_, v_as_1482_, v_sz_boxed_1493_, v_i_boxed_1494_, v_b_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec_ref(v_as_1482_);
lean_dec_ref(v___x_1480_);
return v_res_1495_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__1));
v___x_1499_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__0));
v___x_1500_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1499_, v___x_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object* v_declName_1503_, uint8_t v_isMeta_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v_env_1516_; lean_object* v___y_1518_; lean_object* v___x_1531_; 
v___x_1512_ = lean_st_ref_get(v___y_1510_);
v_env_1516_ = lean_ctor_get(v___x_1512_, 0);
lean_inc_ref(v_env_1516_);
lean_dec(v___x_1512_);
v___x_1531_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1516_, v_declName_1503_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_dec_ref(v_env_1516_);
lean_dec(v_declName_1503_);
goto v___jp_1513_;
}
else
{
lean_object* v_val_1532_; lean_object* v___x_1533_; lean_object* v_modules_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_val_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref(v___x_1531_);
v___x_1533_ = l_Lean_Environment_header(v_env_1516_);
v_modules_1534_ = lean_ctor_get(v___x_1533_, 3);
lean_inc_ref(v_modules_1534_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = lean_array_get_size(v_modules_1534_);
v___x_1536_ = lean_nat_dec_lt(v_val_1532_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec_ref(v_modules_1534_);
lean_dec(v_val_1532_);
lean_dec_ref(v_env_1516_);
lean_dec(v_declName_1503_);
goto v___jp_1513_;
}
else
{
lean_object* v___x_1537_; lean_object* v_env_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___y_1542_; 
v___x_1537_ = lean_st_ref_get(v___y_1510_);
v_env_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc_ref(v_env_1538_);
lean_dec(v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2);
v___x_1540_ = lean_array_fget(v_modules_1534_, v_val_1532_);
lean_dec(v_val_1532_);
lean_dec_ref(v_modules_1534_);
if (v_isMeta_1504_ == 0)
{
lean_dec_ref(v_env_1538_);
v___y_1542_ = v_isMeta_1504_;
goto v___jp_1541_;
}
else
{
uint8_t v___x_1553_; 
lean_inc(v_declName_1503_);
v___x_1553_ = l_Lean_isMarkedMeta(v_env_1538_, v_declName_1503_);
if (v___x_1553_ == 0)
{
v___y_1542_ = v_isMeta_1504_;
goto v___jp_1541_;
}
else
{
uint8_t v___x_1554_; 
v___x_1554_ = 0;
v___y_1542_ = v___x_1554_;
goto v___jp_1541_;
}
}
v___jp_1541_:
{
lean_object* v_toImport_1543_; lean_object* v_module_1544_; lean_object* v___x_1545_; 
v_toImport_1543_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref(v_toImport_1543_);
lean_dec(v___x_1540_);
v_module_1544_ = lean_ctor_get(v_toImport_1543_, 0);
lean_inc(v_module_1544_);
lean_dec_ref(v_toImport_1543_);
lean_inc(v_declName_1503_);
v___x_1545_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5(v_module_1544_, v___y_1542_, v_declName_1503_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec_ref(v___x_1545_);
v___x_1546_ = l_Lean_indirectModUseExt;
v___x_1547_ = lean_box(1);
v___x_1548_ = lean_box(0);
lean_inc_ref(v_env_1516_);
v___x_1549_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1539_, v___x_1546_, v_env_1516_, v___x_1547_, v___x_1548_);
v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_1549_, v_declName_1503_);
lean_dec(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__3));
v___y_1518_ = v___x_1551_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref(v___x_1550_);
v___y_1518_ = v_val_1552_;
goto v___jp_1517_;
}
}
else
{
lean_dec_ref(v_env_1516_);
lean_dec(v_declName_1503_);
return v___x_1545_;
}
}
}
}
v___jp_1513_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
v___jp_1517_:
{
lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = lean_box(0);
v_sz_1520_ = lean_array_size(v___y_1518_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__6(v_env_1516_, v_declName_1503_, v___y_1518_, v_sz_1520_, v___x_1521_, v___x_1519_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v_env_1516_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1522_, 0);
lean_dec(v_unused_1530_);
v___x_1524_ = v___x_1522_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_dec(v___x_1522_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1519_);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1519_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
else
{
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object* v_declName_1555_, lean_object* v_isMeta_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v_isMeta_boxed_1564_; lean_object* v_res_1565_; 
v_isMeta_boxed_1564_ = lean_unbox(v_isMeta_1556_);
v_res_1565_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_declName_1555_, v_isMeta_boxed_1564_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg(lean_object* v_as_x27_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
if (lean_obj_tag(v_as_x27_1566_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_b_1567_);
return v___x_1575_;
}
else
{
lean_object* v_head_1576_; lean_object* v_tail_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v_head_1576_ = lean_ctor_get(v_as_x27_1566_, 0);
lean_inc(v_head_1576_);
v_tail_1577_ = lean_ctor_get(v_as_x27_1566_, 1);
lean_inc(v_tail_1577_);
lean_dec_ref(v_as_x27_1566_);
v___x_1578_ = 1;
v___x_1579_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_head_1576_, v___x_1578_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v___x_1579_);
v___x_1580_ = lean_box(0);
v_as_x27_1566_ = v_tail_1577_;
v_b_1567_ = v___x_1580_;
goto _start;
}
else
{
lean_dec(v_tail_1577_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg___boxed(lean_object* v_as_x27_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg(v_as_x27_1582_, v_b_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object* v_env_1592_, lean_object* v_currNamespace_1593_, lean_object* v_openDecls_1594_, lean_object* v_n_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Lean_ResolveName_resolveNamespace(v_env_1592_, v_currNamespace_1593_, v_openDecls_1594_, v_n_1595_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object* v_env_1600_, lean_object* v_currNamespace_1601_, lean_object* v_openDecls_1602_, lean_object* v_n_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_1600_, v_currNamespace_1601_, v_openDecls_1602_, v_n_1603_, v___y_1604_, v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v_env_1617_; lean_object* v_options_1618_; lean_object* v_currRecDepth_1619_; lean_object* v_maxRecDepth_1620_; lean_object* v_ref_1621_; lean_object* v_currNamespace_1622_; lean_object* v_openDecls_1623_; lean_object* v_quotContext_1624_; lean_object* v_currMacroScope_1625_; lean_object* v___x_1626_; lean_object* v_nextMacroScope_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; lean_object* v___f_1630_; lean_object* v___f_1631_; lean_object* v___f_1632_; lean_object* v_methods_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1616_ = lean_st_ref_get(v___y_1614_);
v_env_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc_ref(v_env_1617_);
lean_dec(v___x_1616_);
v_options_1618_ = lean_ctor_get(v___y_1613_, 2);
v_currRecDepth_1619_ = lean_ctor_get(v___y_1613_, 3);
v_maxRecDepth_1620_ = lean_ctor_get(v___y_1613_, 4);
v_ref_1621_ = lean_ctor_get(v___y_1613_, 5);
v_currNamespace_1622_ = lean_ctor_get(v___y_1613_, 6);
v_openDecls_1623_ = lean_ctor_get(v___y_1613_, 7);
v_quotContext_1624_ = lean_ctor_get(v___y_1613_, 10);
v_currMacroScope_1625_ = lean_ctor_get(v___y_1613_, 11);
v___x_1626_ = lean_st_ref_get(v___y_1614_);
v_nextMacroScope_1627_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_nextMacroScope_1627_);
lean_dec(v___x_1626_);
lean_inc_ref(v_env_1617_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1628_, 0, v_env_1617_);
lean_inc_ref(v_env_1617_);
v___f_1629_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1629_, 0, v_env_1617_);
lean_inc(v_openDecls_1623_);
lean_inc(v_currNamespace_1622_);
lean_inc_ref(v_env_1617_);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1630_, 0, v_env_1617_);
lean_closure_set(v___f_1630_, 1, v_currNamespace_1622_);
lean_closure_set(v___f_1630_, 2, v_openDecls_1623_);
lean_inc(v_currNamespace_1622_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1631_, 0, v_currNamespace_1622_);
lean_inc(v_openDecls_1623_);
lean_inc(v_currNamespace_1622_);
lean_inc_ref(v_options_1618_);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1632_, 0, v_env_1617_);
lean_closure_set(v___f_1632_, 1, v_options_1618_);
lean_closure_set(v___f_1632_, 2, v_currNamespace_1622_);
lean_closure_set(v___f_1632_, 3, v_openDecls_1623_);
v_methods_1633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1633_, 0, v___f_1628_);
lean_ctor_set(v_methods_1633_, 1, v___f_1631_);
lean_ctor_set(v_methods_1633_, 2, v___f_1629_);
lean_ctor_set(v_methods_1633_, 3, v___f_1630_);
lean_ctor_set(v_methods_1633_, 4, v___f_1632_);
lean_inc(v_ref_1621_);
lean_inc(v_maxRecDepth_1620_);
lean_inc(v_currRecDepth_1619_);
lean_inc(v_currMacroScope_1625_);
lean_inc(v_quotContext_1624_);
v___x_1634_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1634_, 0, v_methods_1633_);
lean_ctor_set(v___x_1634_, 1, v_quotContext_1624_);
lean_ctor_set(v___x_1634_, 2, v_currMacroScope_1625_);
lean_ctor_set(v___x_1634_, 3, v_currRecDepth_1619_);
lean_ctor_set(v___x_1634_, 4, v_maxRecDepth_1620_);
lean_ctor_set(v___x_1634_, 5, v_ref_1621_);
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1636_, 0, v_nextMacroScope_1627_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_ctor_set(v___x_1636_, 2, v___x_1635_);
v___x_1637_ = lean_apply_2(v_x_1608_, v___x_1634_, v___x_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_a_1639_; lean_object* v_macroScope_1640_; lean_object* v_traceMsgs_1641_; lean_object* v_expandedMacroDecls_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 1);
lean_inc(v_a_1638_);
v_a_1639_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1637_);
v_macroScope_1640_ = lean_ctor_get(v_a_1638_, 0);
lean_inc(v_macroScope_1640_);
v_traceMsgs_1641_ = lean_ctor_get(v_a_1638_, 1);
lean_inc(v_traceMsgs_1641_);
v_expandedMacroDecls_1642_ = lean_ctor_get(v_a_1638_, 2);
lean_inc(v_expandedMacroDecls_1642_);
lean_dec(v_a_1638_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg(v_expandedMacroDecls_1642_, v___x_1643_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; lean_object* v_env_1646_; lean_object* v_ngen_1647_; lean_object* v_auxDeclNGen_1648_; lean_object* v_traceState_1649_; lean_object* v_cache_1650_; lean_object* v_messages_1651_; lean_object* v_infoState_1652_; lean_object* v_snapshotTasks_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v___x_1644_);
v___x_1645_ = lean_st_ref_take(v___y_1614_);
v_env_1646_ = lean_ctor_get(v___x_1645_, 0);
v_ngen_1647_ = lean_ctor_get(v___x_1645_, 2);
v_auxDeclNGen_1648_ = lean_ctor_get(v___x_1645_, 3);
v_traceState_1649_ = lean_ctor_get(v___x_1645_, 4);
v_cache_1650_ = lean_ctor_get(v___x_1645_, 5);
v_messages_1651_ = lean_ctor_get(v___x_1645_, 6);
v_infoState_1652_ = lean_ctor_get(v___x_1645_, 7);
v_snapshotTasks_1653_ = lean_ctor_get(v___x_1645_, 8);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1645_, 1);
lean_dec(v_unused_1680_);
v___x_1655_ = v___x_1645_;
v_isShared_1656_ = v_isSharedCheck_1679_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snapshotTasks_1653_);
lean_inc(v_infoState_1652_);
lean_inc(v_messages_1651_);
lean_inc(v_cache_1650_);
lean_inc(v_traceState_1649_);
lean_inc(v_auxDeclNGen_1648_);
lean_inc(v_ngen_1647_);
lean_inc(v_env_1646_);
lean_dec(v___x_1645_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1679_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_macroScope_1640_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_env_1646_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_macroScope_1640_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_ngen_1647_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_auxDeclNGen_1648_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v_traceState_1649_);
lean_ctor_set(v_reuseFailAlloc_1678_, 5, v_cache_1650_);
lean_ctor_set(v_reuseFailAlloc_1678_, 6, v_messages_1651_);
lean_ctor_set(v_reuseFailAlloc_1678_, 7, v_infoState_1652_);
lean_ctor_set(v_reuseFailAlloc_1678_, 8, v_snapshotTasks_1653_);
v___x_1658_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_st_ref_set(v___y_1614_, v___x_1658_);
v___x_1660_ = l_List_reverse___redArg(v_traceMsgs_1641_);
v___x_1661_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v___x_1660_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v___y_1609_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1661_, 0);
lean_dec(v_unused_1669_);
v___x_1663_ = v___x_1661_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_dec(v___x_1661_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v_a_1639_);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1639_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_a_1639_);
v_a_1670_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1661_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1661_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_traceMsgs_1641_);
lean_dec(v_macroScope_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v___y_1609_);
v_a_1681_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1644_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1644_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; 
v_a_1689_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1689_);
lean_dec_ref(v___x_1637_);
if (lean_obj_tag(v_a_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v_a_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_a_1690_ = lean_ctor_get(v_a_1689_, 0);
lean_inc(v_a_1690_);
v_a_1691_ = lean_ctor_get(v_a_1689_, 1);
lean_inc_ref(v_a_1691_);
lean_dec_ref(v_a_1689_);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0));
v___x_1693_ = lean_string_dec_eq(v_a_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1691_);
v___x_1695_ = l_Lean_MessageData_ofFormat(v___x_1694_);
v___x_1696_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_1690_, v___x_1695_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v_a_1690_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; 
lean_dec_ref(v_a_1691_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v___y_1609_);
v___x_1697_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(v_a_1690_);
return v___x_1697_;
}
}
else
{
lean_object* v___x_1698_; 
lean_dec_ref(v___y_1613_);
lean_dec_ref(v___y_1609_);
v___x_1698_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg();
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* v_x_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg(lean_object* v_t_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v_infoState_1712_; uint8_t v_enabled_1713_; 
v___x_1711_ = lean_st_ref_get(v___y_1709_);
v_infoState_1712_ = lean_ctor_get(v___x_1711_, 7);
lean_inc_ref(v_infoState_1712_);
lean_dec(v___x_1711_);
v_enabled_1713_ = lean_ctor_get_uint8(v_infoState_1712_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1712_);
if (v_enabled_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v_t_1708_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v_infoState_1717_; lean_object* v_env_1718_; lean_object* v_nextMacroScope_1719_; lean_object* v_ngen_1720_; lean_object* v_auxDeclNGen_1721_; lean_object* v_traceState_1722_; lean_object* v_cache_1723_; lean_object* v_messages_1724_; lean_object* v_snapshotTasks_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1747_; 
v___x_1716_ = lean_st_ref_take(v___y_1709_);
v_infoState_1717_ = lean_ctor_get(v___x_1716_, 7);
v_env_1718_ = lean_ctor_get(v___x_1716_, 0);
v_nextMacroScope_1719_ = lean_ctor_get(v___x_1716_, 1);
v_ngen_1720_ = lean_ctor_get(v___x_1716_, 2);
v_auxDeclNGen_1721_ = lean_ctor_get(v___x_1716_, 3);
v_traceState_1722_ = lean_ctor_get(v___x_1716_, 4);
v_cache_1723_ = lean_ctor_get(v___x_1716_, 5);
v_messages_1724_ = lean_ctor_get(v___x_1716_, 6);
v_snapshotTasks_1725_ = lean_ctor_get(v___x_1716_, 8);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1727_ = v___x_1716_;
v_isShared_1728_ = v_isSharedCheck_1747_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snapshotTasks_1725_);
lean_inc(v_infoState_1717_);
lean_inc(v_messages_1724_);
lean_inc(v_cache_1723_);
lean_inc(v_traceState_1722_);
lean_inc(v_auxDeclNGen_1721_);
lean_inc(v_ngen_1720_);
lean_inc(v_nextMacroScope_1719_);
lean_inc(v_env_1718_);
lean_dec(v___x_1716_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1747_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
uint8_t v_enabled_1729_; lean_object* v_assignment_1730_; lean_object* v_lazyAssignment_1731_; lean_object* v_trees_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1746_; 
v_enabled_1729_ = lean_ctor_get_uint8(v_infoState_1717_, sizeof(void*)*3);
v_assignment_1730_ = lean_ctor_get(v_infoState_1717_, 0);
v_lazyAssignment_1731_ = lean_ctor_get(v_infoState_1717_, 1);
v_trees_1732_ = lean_ctor_get(v_infoState_1717_, 2);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_infoState_1717_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1734_ = v_infoState_1717_;
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_trees_1732_);
lean_inc(v_lazyAssignment_1731_);
lean_inc(v_assignment_1730_);
lean_dec(v_infoState_1717_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = l_Lean_PersistentArray_push___redArg(v_trees_1732_, v_t_1708_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 2, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_assignment_1730_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_lazyAssignment_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v___x_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1745_, sizeof(void*)*3, v_enabled_1729_);
v___x_1738_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 7, v___x_1738_);
v___x_1740_ = v___x_1727_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_env_1718_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_nextMacroScope_1719_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_ngen_1720_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_auxDeclNGen_1721_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v_traceState_1722_);
lean_ctor_set(v_reuseFailAlloc_1744_, 5, v_cache_1723_);
lean_ctor_set(v_reuseFailAlloc_1744_, 6, v_messages_1724_);
lean_ctor_set(v_reuseFailAlloc_1744_, 7, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1744_, 8, v_snapshotTasks_1725_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_st_ref_set(v___y_1709_, v___x_1740_);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg___boxed(lean_object* v_t_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg(v_t_1748_, v___y_1749_);
lean_dec(v___y_1749_);
return v_res_1751_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_unsigned_to_nat(32u);
v___x_1753_ = lean_mk_empty_array_with_capacity(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1(void){
_start:
{
size_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1755_ = ((size_t)5ULL);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_unsigned_to_nat(32u);
v___x_1758_ = lean_mk_empty_array_with_capacity(v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
v___x_1760_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1758_);
lean_ctor_set(v___x_1760_, 2, v___x_1756_);
lean_ctor_set(v___x_1760_, 3, v___x_1756_);
lean_ctor_set_usize(v___x_1760_, 4, v___x_1755_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object* v_t_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_infoState_1770_; uint8_t v_enabled_1771_; 
v___x_1769_ = lean_st_ref_get(v___y_1767_);
v_infoState_1770_ = lean_ctor_get(v___x_1769_, 7);
lean_inc_ref(v_infoState_1770_);
lean_dec(v___x_1769_);
v_enabled_1771_ = lean_ctor_get_uint8(v_infoState_1770_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1770_);
if (v_enabled_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec_ref(v_t_1761_);
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
v___x_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_t_1761_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg(v___x_1775_, v___y_1767_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object* v_t_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v_t_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object* v_info_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_info_1786_);
v___x_1795_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_1794_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object* v_info_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1804_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0(uint8_t v___y_1812_, uint8_t v_suppressElabErrors_1813_, lean_object* v_x_1814_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 1)
{
lean_object* v_pre_1815_; 
v_pre_1815_ = lean_ctor_get(v_x_1814_, 0);
switch(lean_obj_tag(v_pre_1815_))
{
case 1:
{
lean_object* v_pre_1816_; 
v_pre_1816_ = lean_ctor_get(v_pre_1815_, 0);
switch(lean_obj_tag(v_pre_1816_))
{
case 0:
{
lean_object* v_str_1817_; lean_object* v_str_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_str_1817_ = lean_ctor_get(v_x_1814_, 1);
v_str_1818_ = lean_ctor_get(v_pre_1815_, 1);
v___x_1819_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__0));
v___x_1820_ = lean_string_dec_eq(v_str_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__1));
v___x_1822_ = lean_string_dec_eq(v_str_1818_, v___x_1821_);
if (v___x_1822_ == 0)
{
return v___y_1812_;
}
else
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__2));
v___x_1824_ = lean_string_dec_eq(v_str_1817_, v___x_1823_);
if (v___x_1824_ == 0)
{
return v___y_1812_;
}
else
{
return v_suppressElabErrors_1813_;
}
}
}
else
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__3));
v___x_1826_ = lean_string_dec_eq(v_str_1817_, v___x_1825_);
if (v___x_1826_ == 0)
{
return v___y_1812_;
}
else
{
return v_suppressElabErrors_1813_;
}
}
}
case 1:
{
lean_object* v_pre_1827_; 
v_pre_1827_ = lean_ctor_get(v_pre_1816_, 0);
if (lean_obj_tag(v_pre_1827_) == 0)
{
lean_object* v_str_1828_; lean_object* v_str_1829_; lean_object* v_str_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_str_1828_ = lean_ctor_get(v_x_1814_, 1);
v_str_1829_ = lean_ctor_get(v_pre_1815_, 1);
v_str_1830_ = lean_ctor_get(v_pre_1816_, 1);
v___x_1831_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__4));
v___x_1832_ = lean_string_dec_eq(v_str_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
return v___y_1812_;
}
else
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__5));
v___x_1834_ = lean_string_dec_eq(v_str_1829_, v___x_1833_);
if (v___x_1834_ == 0)
{
return v___y_1812_;
}
else
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___closed__6));
v___x_1836_ = lean_string_dec_eq(v_str_1828_, v___x_1835_);
if (v___x_1836_ == 0)
{
return v___y_1812_;
}
else
{
return v_suppressElabErrors_1813_;
}
}
}
}
else
{
return v___y_1812_;
}
}
default: 
{
return v___y_1812_;
}
}
}
case 0:
{
lean_object* v_str_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_str_1837_ = lean_ctor_get(v_x_1814_, 1);
v___x_1838_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0));
v___x_1839_ = lean_string_dec_eq(v_str_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
return v___y_1812_;
}
else
{
return v_suppressElabErrors_1813_;
}
}
default: 
{
return v___y_1812_;
}
}
}
else
{
return v___y_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___y_1840_, lean_object* v_suppressElabErrors_1841_, lean_object* v_x_1842_){
_start:
{
uint8_t v___y_21271__boxed_1843_; uint8_t v_suppressElabErrors_boxed_1844_; uint8_t v_res_1845_; lean_object* v_r_1846_; 
v___y_21271__boxed_1843_ = lean_unbox(v___y_1840_);
v_suppressElabErrors_boxed_1844_ = lean_unbox(v_suppressElabErrors_1841_);
v_res_1845_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0(v___y_21271__boxed_1843_, v_suppressElabErrors_boxed_1844_, v_x_1842_);
lean_dec(v_x_1842_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg(lean_object* v_ref_1847_, lean_object* v_msgData_1848_, uint8_t v_severity_1849_, uint8_t v_isSilent_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___y_1857_; lean_object* v___y_1858_; uint8_t v___y_1859_; uint8_t v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1893_; uint8_t v___y_1894_; uint8_t v___y_1895_; uint8_t v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1918_; lean_object* v___y_1919_; uint8_t v___y_1920_; uint8_t v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1929_; uint8_t v___y_1930_; uint8_t v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; uint8_t v___x_1940_; lean_object* v___y_1942_; uint8_t v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; uint8_t v___y_1947_; uint8_t v___y_1948_; uint8_t v___y_1950_; uint8_t v___x_1965_; 
v___x_1940_ = 2;
v___x_1965_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1849_, v___x_1940_);
if (v___x_1965_ == 0)
{
v___y_1950_ = v___x_1965_;
goto v___jp_1949_;
}
else
{
uint8_t v___x_1966_; 
lean_inc_ref(v_msgData_1848_);
v___x_1966_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1848_);
v___y_1950_ = v___x_1966_;
goto v___jp_1949_;
}
v___jp_1856_:
{
lean_object* v___x_1866_; lean_object* v_currNamespace_1867_; lean_object* v_openDecls_1868_; lean_object* v_env_1869_; lean_object* v_nextMacroScope_1870_; lean_object* v_ngen_1871_; lean_object* v_auxDeclNGen_1872_; lean_object* v_traceState_1873_; lean_object* v_cache_1874_; lean_object* v_messages_1875_; lean_object* v_infoState_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1891_; 
v___x_1866_ = lean_st_ref_take(v___y_1865_);
v_currNamespace_1867_ = lean_ctor_get(v___y_1864_, 6);
lean_inc(v_currNamespace_1867_);
v_openDecls_1868_ = lean_ctor_get(v___y_1864_, 7);
lean_inc(v_openDecls_1868_);
lean_dec_ref(v___y_1864_);
v_env_1869_ = lean_ctor_get(v___x_1866_, 0);
v_nextMacroScope_1870_ = lean_ctor_get(v___x_1866_, 1);
v_ngen_1871_ = lean_ctor_get(v___x_1866_, 2);
v_auxDeclNGen_1872_ = lean_ctor_get(v___x_1866_, 3);
v_traceState_1873_ = lean_ctor_get(v___x_1866_, 4);
v_cache_1874_ = lean_ctor_get(v___x_1866_, 5);
v_messages_1875_ = lean_ctor_get(v___x_1866_, 6);
v_infoState_1876_ = lean_ctor_get(v___x_1866_, 7);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1866_, 8);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1879_ = v___x_1866_;
v_isShared_1880_ = v_isSharedCheck_1891_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1876_);
lean_inc(v_messages_1875_);
lean_inc(v_cache_1874_);
lean_inc(v_traceState_1873_);
lean_inc(v_auxDeclNGen_1872_);
lean_inc(v_ngen_1871_);
lean_inc(v_nextMacroScope_1870_);
lean_inc(v_env_1869_);
lean_dec(v___x_1866_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1891_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_currNamespace_1867_);
lean_ctor_set(v___x_1881_, 1, v_openDecls_1868_);
v___x_1882_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___y_1857_);
v___x_1883_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1883_, 0, v___y_1862_);
lean_ctor_set(v___x_1883_, 1, v___y_1858_);
lean_ctor_set(v___x_1883_, 2, v___y_1861_);
lean_ctor_set(v___x_1883_, 3, v___y_1863_);
lean_ctor_set(v___x_1883_, 4, v___x_1882_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*5, v___y_1860_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*5 + 1, v___y_1859_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*5 + 2, v_isSilent_1850_);
v___x_1884_ = l_Lean_MessageLog_add(v___x_1883_, v_messages_1875_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 6, v___x_1884_);
v___x_1886_ = v___x_1879_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_env_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_nextMacroScope_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_ngen_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_auxDeclNGen_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_traceState_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_infoState_1876_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_snapshotTasks_1877_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_st_ref_set(v___y_1865_, v___x_1886_);
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
}
v___jp_1892_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1916_; 
v___x_1901_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1848_);
v___x_1902_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v___x_1901_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_inc_ref(v___y_1899_);
v___x_1907_ = l_Lean_FileMap_toPosition(v___y_1899_, v___y_1897_);
lean_dec(v___y_1897_);
v___x_1908_ = l_Lean_FileMap_toPosition(v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1));
if (v___y_1895_ == 0)
{
lean_del_object(v___x_1905_);
lean_dec_ref(v___y_1893_);
v___y_1857_ = v_a_1903_;
v___y_1858_ = v___x_1907_;
v___y_1859_ = v___y_1894_;
v___y_1860_ = v___y_1896_;
v___y_1861_ = v___x_1909_;
v___y_1862_ = v___y_1898_;
v___y_1863_ = v___x_1910_;
v___y_1864_ = v___y_1853_;
v___y_1865_ = v___y_1854_;
goto v___jp_1856_;
}
else
{
uint8_t v___x_1911_; 
lean_inc(v_a_1903_);
v___x_1911_ = l_Lean_MessageData_hasTag(v___y_1893_, v_a_1903_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_dec_ref(v___x_1909_);
lean_dec_ref(v___x_1907_);
lean_dec(v_a_1903_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v___y_1853_);
v___x_1912_ = lean_box(0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1912_);
v___x_1914_ = v___x_1905_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
else
{
lean_del_object(v___x_1905_);
v___y_1857_ = v_a_1903_;
v___y_1858_ = v___x_1907_;
v___y_1859_ = v___y_1894_;
v___y_1860_ = v___y_1896_;
v___y_1861_ = v___x_1909_;
v___y_1862_ = v___y_1898_;
v___y_1863_ = v___x_1910_;
v___y_1864_ = v___y_1853_;
v___y_1865_ = v___y_1854_;
goto v___jp_1856_;
}
}
}
}
v___jp_1917_:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Syntax_getTailPos_x3f(v___y_1919_, v___y_1921_);
lean_dec(v___y_1919_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_inc(v___y_1925_);
v___y_1893_ = v___y_1918_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1922_;
v___y_1896_ = v___y_1921_;
v___y_1897_ = v___y_1925_;
v___y_1898_ = v___y_1923_;
v___y_1899_ = v___y_1924_;
v___y_1900_ = v___y_1925_;
goto v___jp_1892_;
}
else
{
lean_object* v_val_1927_; 
v_val_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_val_1927_);
lean_dec_ref(v___x_1926_);
v___y_1893_ = v___y_1918_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1922_;
v___y_1896_ = v___y_1921_;
v___y_1897_ = v___y_1925_;
v___y_1898_ = v___y_1923_;
v___y_1899_ = v___y_1924_;
v___y_1900_ = v_val_1927_;
goto v___jp_1892_;
}
}
v___jp_1928_:
{
lean_object* v_ref_1936_; lean_object* v___x_1937_; 
v_ref_1936_ = l_Lean_replaceRef(v_ref_1847_, v___y_1933_);
lean_dec(v___y_1933_);
v___x_1937_ = l_Lean_Syntax_getPos_x3f(v_ref_1936_, v___y_1931_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_unsigned_to_nat(0u);
v___y_1918_ = v___y_1929_;
v___y_1919_ = v_ref_1936_;
v___y_1920_ = v___y_1935_;
v___y_1921_ = v___y_1931_;
v___y_1922_ = v___y_1930_;
v___y_1923_ = v___y_1932_;
v___y_1924_ = v___y_1934_;
v___y_1925_ = v___x_1938_;
goto v___jp_1917_;
}
else
{
lean_object* v_val_1939_; 
v_val_1939_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_val_1939_);
lean_dec_ref(v___x_1937_);
v___y_1918_ = v___y_1929_;
v___y_1919_ = v_ref_1936_;
v___y_1920_ = v___y_1935_;
v___y_1921_ = v___y_1931_;
v___y_1922_ = v___y_1930_;
v___y_1923_ = v___y_1932_;
v___y_1924_ = v___y_1934_;
v___y_1925_ = v_val_1939_;
goto v___jp_1917_;
}
}
v___jp_1941_:
{
if (v___y_1948_ == 0)
{
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1943_;
v___y_1931_ = v___y_1947_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___y_1944_;
v___y_1934_ = v___y_1946_;
v___y_1935_ = v_severity_1849_;
goto v___jp_1928_;
}
else
{
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1943_;
v___y_1931_ = v___y_1947_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___y_1944_;
v___y_1934_ = v___y_1946_;
v___y_1935_ = v___x_1940_;
goto v___jp_1928_;
}
}
v___jp_1949_:
{
if (v___y_1950_ == 0)
{
lean_object* v_fileName_1951_; lean_object* v_fileMap_1952_; lean_object* v_options_1953_; lean_object* v_ref_1954_; uint8_t v_suppressElabErrors_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___f_1958_; uint8_t v___x_1959_; uint8_t v___x_1960_; 
v_fileName_1951_ = lean_ctor_get(v___y_1853_, 0);
v_fileMap_1952_ = lean_ctor_get(v___y_1853_, 1);
v_options_1953_ = lean_ctor_get(v___y_1853_, 2);
v_ref_1954_ = lean_ctor_get(v___y_1853_, 5);
v_suppressElabErrors_1955_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*14 + 1);
v___x_1956_ = lean_box(v___y_1950_);
v___x_1957_ = lean_box(v_suppressElabErrors_1955_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1958_, 0, v___x_1956_);
lean_closure_set(v___f_1958_, 1, v___x_1957_);
v___x_1959_ = 1;
v___x_1960_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1849_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_inc_ref(v_fileMap_1952_);
lean_inc_ref(v_fileName_1951_);
lean_inc(v_ref_1954_);
v___y_1942_ = v___f_1958_;
v___y_1943_ = v_suppressElabErrors_1955_;
v___y_1944_ = v_ref_1954_;
v___y_1945_ = v_fileName_1951_;
v___y_1946_ = v_fileMap_1952_;
v___y_1947_ = v___y_1950_;
v___y_1948_ = v___x_1960_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = l_Lean_warningAsError;
v___x_1962_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17(v_options_1953_, v___x_1961_);
lean_inc_ref(v_fileMap_1952_);
lean_inc_ref(v_fileName_1951_);
lean_inc(v_ref_1954_);
v___y_1942_ = v___f_1958_;
v___y_1943_ = v_suppressElabErrors_1955_;
v___y_1944_ = v_ref_1954_;
v___y_1945_ = v_fileName_1951_;
v___y_1946_ = v_fileMap_1952_;
v___y_1947_ = v___y_1950_;
v___y_1948_ = v___x_1962_;
goto v___jp_1941_;
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v___y_1853_);
lean_dec_ref(v_msgData_1848_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg___boxed(lean_object* v_ref_1967_, lean_object* v_msgData_1968_, lean_object* v_severity_1969_, lean_object* v_isSilent_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v_severity_boxed_1976_; uint8_t v_isSilent_boxed_1977_; lean_object* v_res_1978_; 
v_severity_boxed_1976_ = lean_unbox(v_severity_1969_);
v_isSilent_boxed_1977_ = lean_unbox(v_isSilent_1970_);
v_res_1978_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg(v_ref_1967_, v_msgData_1968_, v_severity_boxed_1976_, v_isSilent_boxed_1977_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v_ref_1967_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object* v_ref_1979_, lean_object* v_msgData_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = 2;
v___x_1989_ = 0;
v___x_1990_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg(v_ref_1979_, v_msgData_1980_, v___x_1988_, v___x_1989_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object* v_ref_1991_, lean_object* v_msgData_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v_ref_1991_, v_msgData_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v_ref_1991_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object* v_ref_2001_, lean_object* v_msgData_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = 1;
v___x_2011_ = 0;
v___x_2012_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg(v_ref_2001_, v_msgData_2002_, v___x_2010_, v___x_2011_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object* v_ref_2013_, lean_object* v_msgData_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v_ref_2013_, v_msgData_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v_ref_2013_);
return v_res_2022_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10));
v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12));
v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14));
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* v_stx_2050_, lean_object* v_expType_x3f_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
uint8_t v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v_fst_2152_; lean_object* v_snd_2153_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; uint8_t v___y_2181_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_inc(v_stx_2050_);
v___x_2199_ = l_Lean_Syntax_getKind(v_stx_2050_);
v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_2198_, v___x_2199_);
lean_dec(v___x_2199_);
if (lean_obj_tag(v___x_2200_) == 1)
{
lean_object* v_val_2201_; lean_object* v_fst_2202_; lean_object* v_snd_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2234_; 
v_val_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_val_2201_);
lean_dec_ref(v___x_2200_);
v_fst_2202_ = lean_ctor_get(v_val_2201_, 0);
v_snd_2203_ = lean_ctor_get(v_val_2201_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_val_2201_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2205_ = v_val_2201_;
v_isShared_2206_ = v_isSharedCheck_2234_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_snd_2203_);
lean_inc(v_fst_2202_);
lean_dec(v_val_2201_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2234_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v_env_2208_; uint8_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2207_ = lean_st_ref_get(v_a_2057_);
v_env_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = 1;
lean_inc(v_snd_2203_);
v___x_2210_ = l_Lean_Environment_contains(v_env_2208_, v_snd_2203_, v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_dec(v_expType_x3f_2051_);
lean_dec(v_stx_2050_);
v___x_2211_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
v___x_2212_ = l_Lean_MessageData_ofName(v_snd_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set_tag(v___x_2205_, 7);
lean_ctor_set(v___x_2205_, 1, v___x_2212_);
lean_ctor_set(v___x_2205_, 0, v___x_2211_);
v___x_2214_ = v___x_2205_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
v___x_2215_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
v___x_2218_ = l_Lean_MessageData_ofName(v_fst_2202_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_MessageData_hint_x27(v___x_2221_);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2216_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_2223_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_del_object(v___x_2205_);
lean_dec(v_snd_2203_);
lean_dec(v_fst_2202_);
v___y_2188_ = v_a_2052_;
v___y_2189_ = v_a_2053_;
v___y_2190_ = v_a_2054_;
v___y_2191_ = v_a_2055_;
v___y_2192_ = v_a_2056_;
v___y_2193_ = v_a_2057_;
goto v___jp_2187_;
}
}
}
else
{
lean_dec(v___x_2200_);
v___y_2188_ = v_a_2052_;
v___y_2189_ = v_a_2053_;
v___y_2190_ = v_a_2054_;
v___y_2191_ = v_a_2055_;
v___y_2192_ = v_a_2056_;
v___y_2193_ = v_a_2057_;
goto v___jp_2187_;
}
v___jp_2059_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro), 3, 1);
lean_closure_set(v___x_2067_, 0, v_stx_2050_);
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2061_);
v___x_2068_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_2067_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2070_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2068_);
v___x_2070_ = l_Lean_Elab_Term_elabTerm(v_a_2069_, v_expType_x3f_2051_, v___y_2060_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2070_;
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v_expType_x3f_2051_);
v_a_2071_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2068_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2068_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
v___jp_2079_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_partialId_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2143_; 
v___x_2089_ = l_Lean_Syntax_getNumArgs(v___y_2088_);
v___x_2090_ = lean_unsigned_to_nat(2u);
v___x_2091_ = lean_nat_sub(v___x_2089_, v___x_2090_);
lean_dec(v___x_2089_);
v_partialId_2092_ = l_Lean_Syntax_getArg(v___y_2088_, v___x_2091_);
lean_dec(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___y_2088_);
lean_ctor_set(v___x_2093_, 1, v_partialId_2092_);
v___x_2094_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_2093_, v___y_2082_, v___y_2081_, v___y_2087_, v___y_2080_, v___y_2085_, v___y_2084_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v___x_2094_, 0);
lean_dec(v_unused_2144_);
v___x_2096_ = v___x_2094_;
v_isShared_2097_ = v_isSharedCheck_2143_;
goto v_resetjp_2095_;
}
else
{
lean_dec(v___x_2094_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2143_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2098_ = l_Lean_Syntax_getId(v___y_2083_);
v___x_2099_ = lean_erase_macro_scopes(v___x_2098_);
lean_inc(v___x_2099_);
lean_inc(v___y_2083_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___y_2083_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 6);
lean_ctor_set(v___x_2096_, 0, v___x_2100_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v_a_2105_; 
v___x_2103_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2102_, v___y_2082_, v___y_2081_, v___y_2087_, v___y_2080_, v___y_2085_, v___y_2084_);
lean_dec_ref(v___x_2103_);
v___x_2104_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_2099_, v___y_2084_);
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
if (lean_obj_tag(v_a_2105_) == 1)
{
lean_object* v_val_2106_; lean_object* v_metadata_2107_; lean_object* v_removedVersion_x3f_2108_; 
v_val_2106_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_val_2106_);
lean_dec_ref(v_a_2105_);
v_metadata_2107_ = lean_ctor_get(v_val_2106_, 1);
lean_inc_ref(v_metadata_2107_);
lean_dec(v_val_2106_);
v_removedVersion_x3f_2108_ = lean_ctor_get(v_metadata_2107_, 2);
lean_inc(v_removedVersion_x3f_2108_);
lean_dec_ref(v_metadata_2107_);
if (lean_obj_tag(v_removedVersion_x3f_2108_) == 1)
{
lean_object* v_val_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_val_2109_ = lean_ctor_get(v_removedVersion_x3f_2108_, 0);
lean_inc(v_val_2109_);
lean_dec_ref(v_removedVersion_x3f_2108_);
v___x_2110_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
v___x_2111_ = l_Lean_MessageData_ofName(v___x_2099_);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_stringToMessageData(v_val_2109_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
lean_inc_ref(v___y_2085_);
v___x_2119_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_2083_, v___x_2118_, v___y_2082_, v___y_2081_, v___y_2087_, v___y_2080_, v___y_2085_, v___y_2084_);
lean_dec(v___y_2083_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_dec_ref(v___x_2119_);
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2082_;
v___y_2062_ = v___y_2081_;
v___y_2063_ = v___y_2087_;
v___y_2064_ = v___y_2080_;
v___y_2065_ = v___y_2085_;
v___y_2066_ = v___y_2084_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v___y_2087_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec(v_expType_x3f_2051_);
lean_dec(v_stx_2050_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v_removedVersion_x3f_2108_);
lean_dec(v___x_2099_);
lean_dec(v___y_2083_);
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2082_;
v___y_2062_ = v___y_2081_;
v___y_2063_ = v___y_2087_;
v___y_2064_ = v___y_2080_;
v___y_2065_ = v___y_2085_;
v___y_2066_ = v___y_2084_;
goto v___jp_2059_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec(v_a_2105_);
v___x_2128_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
v___x_2129_ = l_Lean_MessageData_ofName(v___x_2099_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
lean_inc_ref(v___y_2085_);
v___x_2133_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_2083_, v___x_2132_, v___y_2082_, v___y_2081_, v___y_2087_, v___y_2080_, v___y_2085_, v___y_2084_);
lean_dec(v___y_2083_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref(v___x_2133_);
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2082_;
v___y_2062_ = v___y_2081_;
v___y_2063_ = v___y_2087_;
v___y_2064_ = v___y_2080_;
v___y_2065_ = v___y_2085_;
v___y_2066_ = v___y_2084_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___y_2087_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec(v_expType_x3f_2051_);
lean_dec(v_stx_2050_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
}
v___jp_2145_:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = l_Lean_Syntax_getNumArgs(v_stx_2050_);
v___x_2155_ = lean_nat_dec_eq(v___x_2154_, v_snd_2153_);
v___x_2156_ = 1;
if (v___x_2155_ == 0)
{
lean_dec(v___x_2154_);
lean_inc(v_stx_2050_);
v___y_2080_ = v___y_2146_;
v___y_2081_ = v___y_2147_;
v___y_2082_ = v___y_2148_;
v___y_2083_ = v_fst_2152_;
v___y_2084_ = v___y_2150_;
v___y_2085_ = v___y_2149_;
v___y_2086_ = v___x_2156_;
v___y_2087_ = v___y_2151_;
v___y_2088_ = v_stx_2050_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2157_ = l_Lean_Syntax_getArgs(v_stx_2050_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_sub(v___x_2154_, v___x_2158_);
lean_dec(v___x_2154_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = l_Array_toSubarray___redArg(v___x_2157_, v___x_2160_, v___x_2159_);
v___x_2162_ = l_Subarray_copy___redArg(v___x_2161_);
lean_inc(v_stx_2050_);
v___x_2163_ = l_Lean_Syntax_setArgs(v_stx_2050_, v___x_2162_);
v___y_2080_ = v___y_2146_;
v___y_2081_ = v___y_2147_;
v___y_2082_ = v___y_2148_;
v___y_2083_ = v_fst_2152_;
v___y_2084_ = v___y_2150_;
v___y_2085_ = v___y_2149_;
v___y_2086_ = v___x_2156_;
v___y_2087_ = v___y_2151_;
v___y_2088_ = v___x_2163_;
goto v___jp_2079_;
}
}
v___jp_2164_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_unsigned_to_nat(2u);
v___x_2172_ = l_Lean_Syntax_getArg(v_stx_2050_, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(5u);
v___y_2146_ = v___y_2165_;
v___y_2147_ = v___y_2166_;
v___y_2148_ = v___y_2167_;
v___y_2149_ = v___y_2169_;
v___y_2150_ = v___y_2168_;
v___y_2151_ = v___y_2170_;
v_fst_2152_ = v___x_2172_;
v_snd_2153_ = v___x_2173_;
goto v___jp_2145_;
}
v___jp_2174_:
{
if (v___y_2181_ == 0)
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_stx_2050_);
v___x_2183_ = l_Lean_Syntax_isOfKind(v_stx_2050_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = l_Lean_Syntax_getArg(v_stx_2050_, v___x_2184_);
v___x_2186_ = lean_unsigned_to_nat(4u);
v___y_2146_ = v___y_2175_;
v___y_2147_ = v___y_2176_;
v___y_2148_ = v___y_2177_;
v___y_2149_ = v___y_2179_;
v___y_2150_ = v___y_2178_;
v___y_2151_ = v___y_2180_;
v_fst_2152_ = v___x_2185_;
v_snd_2153_ = v___x_2186_;
goto v___jp_2145_;
}
else
{
v___y_2165_ = v___y_2175_;
v___y_2166_ = v___y_2176_;
v___y_2167_ = v___y_2177_;
v___y_2168_ = v___y_2178_;
v___y_2169_ = v___y_2179_;
v___y_2170_ = v___y_2180_;
goto v___jp_2164_;
}
}
else
{
v___y_2165_ = v___y_2175_;
v___y_2166_ = v___y_2176_;
v___y_2167_ = v___y_2177_;
v___y_2168_ = v___y_2178_;
v___y_2169_ = v___y_2179_;
v___y_2170_ = v___y_2180_;
goto v___jp_2164_;
}
}
v___jp_2187_:
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_stx_2050_);
v___x_2195_ = l_Lean_Syntax_isOfKind(v_stx_2050_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_stx_2050_);
v___x_2197_ = l_Lean_Syntax_isOfKind(v_stx_2050_, v___x_2196_);
v___y_2175_ = v___y_2191_;
v___y_2176_ = v___y_2189_;
v___y_2177_ = v___y_2188_;
v___y_2178_ = v___y_2193_;
v___y_2179_ = v___y_2192_;
v___y_2180_ = v___y_2190_;
v___y_2181_ = v___x_2197_;
goto v___jp_2174_;
}
else
{
v___y_2175_ = v___y_2191_;
v___y_2176_ = v___y_2189_;
v___y_2177_ = v___y_2188_;
v___y_2178_ = v___y_2193_;
v___y_2179_ = v___y_2192_;
v___y_2180_ = v___y_2190_;
v___y_2181_ = v___x_2195_;
goto v___jp_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object* v_stx_2235_, lean_object* v_expType_x3f_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(v_stx_2235_, v_expType_x3f_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object* v_cls_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_2245_, v___y_2250_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object* v_cls_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object* v_00_u03b1_2263_, lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___redArg(v_x_2264_, v___y_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_x_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_00_u03b1_2268_, v_x_2269_, v___y_2270_, v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_x_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object* v_00_u03b1_2273_, lean_object* v_ref_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(v_ref_2274_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2283_, lean_object* v_ref_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_2283_, v_ref_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8(lean_object* v_00_u03b1_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg();
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___boxed(lean_object* v_00_u03b1_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8(v_00_u03b1_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* v_00_u03b1_2311_, lean_object* v_x_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* v_00_u03b1_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(v_00_u03b1_2321_, v_x_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11(lean_object* v_t_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___redArg(v_t_2331_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11___boxed(lean_object* v_t_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__11(v_t_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object* v_00_u03b2_2349_, lean_object* v_m_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_2350_, v_a_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object* v_00_u03b2_2353_, lean_object* v_m_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_2353_, v_m_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_m_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object* v_00_u03b1_2357_, lean_object* v_msg_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_msg_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(v_00_u03b1_2367_, v_msg_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object* v_cls_2377_, lean_object* v_msg_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_cls_2377_, v_msg_2378_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object* v_cls_2387_, lean_object* v_msg_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_cls_2387_, v_msg_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object* v_as_2397_, lean_object* v_as_x27_2398_, lean_object* v_b_2399_, lean_object* v_a_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___redArg(v_as_x27_2398_, v_b_2399_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object* v_as_2409_, lean_object* v_as_x27_2410_, lean_object* v_b_2411_, lean_object* v_a_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_2409_, v_as_x27_2410_, v_b_2411_, v_a_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v_as_2409_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object* v_00_u03b1_2421_, lean_object* v_ref_2422_, lean_object* v_msg_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_2422_, v_msg_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_ref_2433_, lean_object* v_msg_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_2432_, v_ref_2433_, v_msg_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec(v_ref_2433_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14(lean_object* v_ref_2443_, lean_object* v_msgData_2444_, uint8_t v_severity_2445_, uint8_t v_isSilent_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___redArg(v_ref_2443_, v_msgData_2444_, v_severity_2445_, v_isSilent_2446_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14___boxed(lean_object* v_ref_2455_, lean_object* v_msgData_2456_, lean_object* v_severity_2457_, lean_object* v_isSilent_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v_severity_boxed_2466_; uint8_t v_isSilent_boxed_2467_; lean_object* v_res_2468_; 
v_severity_boxed_2466_ = lean_unbox(v_severity_2457_);
v_isSilent_boxed_2467_ = lean_unbox(v_isSilent_2458_);
v_res_2468_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14(v_ref_2455_, v_msgData_2456_, v_severity_boxed_2466_, v_isSilent_boxed_2467_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v_ref_2455_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17(lean_object* v_00_u03b2_2469_, lean_object* v_a_2470_, lean_object* v_x_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___redArg(v_a_2470_, v_x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17___boxed(lean_object* v_00_u03b2_2473_, lean_object* v_a_2474_, lean_object* v_x_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__17(v_00_u03b2_2473_, v_a_2474_, v_x_2475_);
lean_dec(v_x_2475_);
lean_dec(v_a_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20(lean_object* v_msgData_2477_, lean_object* v_macroStack_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg(v_msgData_2477_, v_macroStack_2478_, v___y_2483_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___boxed(lean_object* v_msgData_2487_, lean_object* v_macroStack_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20(v_msgData_2487_, v_macroStack_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
return v_res_2496_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16(lean_object* v_00_u03b2_2497_, lean_object* v_x_2498_, lean_object* v_x_2499_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg(v_x_2498_, v_x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___boxed(lean_object* v_00_u03b2_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
uint8_t v_res_2504_; lean_object* v_r_2505_; 
v_res_2504_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16(v_00_u03b2_2501_, v_x_2502_, v_x_2503_);
lean_dec_ref(v_x_2503_);
v_r_2505_ = lean_box(v_res_2504_);
return v_r_2505_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24(lean_object* v_00_u03b2_2506_, lean_object* v_x_2507_, size_t v_x_2508_, lean_object* v_x_2509_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___redArg(v_x_2507_, v_x_2508_, v_x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24___boxed(lean_object* v_00_u03b2_2511_, lean_object* v_x_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_){
_start:
{
size_t v_x_22362__boxed_2515_; uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_x_22362__boxed_2515_ = lean_unbox_usize(v_x_2513_);
lean_dec(v_x_2513_);
v_res_2516_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24(v_00_u03b2_2511_, v_x_2512_, v_x_22362__boxed_2515_, v_x_2514_);
lean_dec_ref(v_x_2514_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27(lean_object* v_00_u03b2_2518_, lean_object* v_keys_2519_, lean_object* v_vals_2520_, lean_object* v_heq_2521_, lean_object* v_i_2522_, lean_object* v_k_2523_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___redArg(v_keys_2519_, v_i_2522_, v_k_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27___boxed(lean_object* v_00_u03b2_2525_, lean_object* v_keys_2526_, lean_object* v_vals_2527_, lean_object* v_heq_2528_, lean_object* v_i_2529_, lean_object* v_k_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16_spec__24_spec__27(v_00_u03b2_2525_, v_keys_2526_, v_vals_2527_, v_heq_2528_, v_i_2529_, v_k_2530_);
lean_dec_ref(v_k_2530_);
lean_dec_ref(v_vals_2527_);
lean_dec_ref(v_keys_2526_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2541_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2542_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
v___x_2543_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2544_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2545_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2541_, v___x_2542_, v___x_2543_, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2549_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2550_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
v___x_2551_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2552_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2553_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2549_, v___x_2550_, v___x_2551_, v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2557_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2558_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
v___x_2559_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2560_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2561_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2557_, v___x_2558_, v___x_2559_, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2565_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2566_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
v___x_2567_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2569_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2565_, v___x_2566_, v___x_2567_, v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2573_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2574_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
v___x_2575_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2576_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2577_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2573_, v___x_2574_, v___x_2575_, v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2581_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2582_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
v___x_2583_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2584_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2585_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2581_, v___x_2582_, v___x_2583_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
return v_res_2587_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
v___x_2589_ = l_Lean_Elab_abortTermExceptionId;
v___x_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___x_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg(){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___boxed(lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(lean_object* v_00_u03b1_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(v_00_u03b1_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* v_t_2614_, lean_object* v_tp_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_inc_ref(v_tp_2615_);
v___x_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_tp_2615_);
v___x_2624_ = 1;
v___x_2625_ = lean_box(0);
lean_inc(v_a_2621_);
lean_inc_ref(v_a_2620_);
lean_inc(v_a_2619_);
lean_inc_ref(v_a_2618_);
v___x_2626_ = l_Lean_Elab_Term_elabTermEnsuringType(v_t_2614_, v___x_2623_, v___x_2624_, v___x_2624_, v___x_2625_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; uint8_t v___x_2635_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
v___x_2635_ = l_Lean_Expr_hasSyntheticSorry(v_a_2627_);
if (v___x_2635_ == 0)
{
v___y_2629_ = v_a_2618_;
v___y_2630_ = v_a_2619_;
v___y_2631_ = v_a_2620_;
v___y_2632_ = v_a_2621_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_dec_ref(v___x_2636_);
v___y_2629_ = v_a_2618_;
v___y_2630_ = v_a_2619_;
v___y_2631_ = v_a_2620_;
v___y_2632_ = v_a_2621_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_a_2627_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec_ref(v_tp_2615_);
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
v___jp_2628_:
{
uint8_t v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = 1;
v___x_2634_ = l_Lean_Meta_evalExpr___redArg(v_tp_2615_, v_a_2627_, v___x_2633_, v___x_2624_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec_ref(v_tp_2615_);
v_a_2645_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2626_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2626_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object* v_t_2653_, lean_object* v_tp_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2653_, v_tp_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg(){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__8___redArg___closed__0);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* v_00_u03b1_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* v_00_u03b1_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; lean_object* v_env_2681_; lean_object* v___x_2682_; lean_object* v_mainModule_2683_; lean_object* v___x_2684_; 
v___x_2680_ = lean_st_ref_get(v___y_2678_);
v_env_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc_ref(v_env_2681_);
lean_dec(v___x_2680_);
v___x_2682_ = l_Lean_Environment_header(v_env_2681_);
lean_dec_ref(v_env_2681_);
v_mainModule_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_mainModule_2683_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_mainModule_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_2685_);
lean_dec(v___y_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* v_t_2696_, lean_object* v___x_2697_, lean_object* v_x_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2696_, v___x_2697_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object* v_t_2707_, lean_object* v___x_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(v_t_2707_, v___x_2708_, v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec_ref(v_x_2709_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(lean_object* v_msgData_2718_, lean_object* v_macroStack_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; lean_object* v_scopes_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v_opts_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2722_ = lean_st_ref_get(v___y_2720_);
v_scopes_2723_ = lean_ctor_get(v___x_2722_, 2);
lean_inc(v_scopes_2723_);
lean_dec(v___x_2722_);
v___x_2724_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2725_ = l_List_head_x21___redArg(v___x_2724_, v_scopes_2723_);
lean_dec(v_scopes_2723_);
v_opts_2726_ = lean_ctor_get(v___x_2725_, 1);
lean_inc_ref(v_opts_2726_);
lean_dec(v___x_2725_);
v___x_2727_ = l_Lean_Elab_pp_macroStack;
v___x_2728_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__14_spec__17(v_opts_2726_, v___x_2727_);
lean_dec_ref(v_opts_2726_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
lean_dec(v_macroStack_2719_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v_msgData_2718_);
return v___x_2729_;
}
else
{
if (lean_obj_tag(v_macroStack_2719_) == 0)
{
lean_object* v___x_2730_; 
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_msgData_2718_);
return v___x_2730_;
}
else
{
lean_object* v_head_2731_; lean_object* v_after_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2747_; 
v_head_2731_ = lean_ctor_get(v_macroStack_2719_, 0);
lean_inc(v_head_2731_);
v_after_2732_ = lean_ctor_get(v_head_2731_, 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_head_2731_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; 
v_unused_2748_ = lean_ctor_get(v_head_2731_, 0);
lean_dec(v_unused_2748_);
v___x_2734_ = v_head_2731_;
v_isShared_2735_ = v_isSharedCheck_2747_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_after_2732_);
lean_dec(v_head_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2747_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2736_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24___closed__0);
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 7);
lean_ctor_set(v___x_2734_, 1, v___x_2736_);
lean_ctor_set(v___x_2734_, 0, v_msgData_2718_);
v___x_2738_ = v___x_2734_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_msgData_2718_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v_msgData_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2739_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20___redArg___closed__2);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofSyntax(v_after_2732_);
v___x_2742_ = l_Lean_indentD(v___x_2741_);
v_msgData_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2743_, 0, v___x_2740_);
lean_ctor_set(v_msgData_2743_, 1, v___x_2742_);
v___x_2744_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__20_spec__24(v_msgData_2743_, v_macroStack_2719_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_2749_, lean_object* v_macroStack_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_2749_, v_macroStack_2750_, v___y_2751_);
lean_dec(v___y_2751_);
return v_res_2753_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2757_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
lean_ctor_set(v___x_2759_, 2, v___x_2758_);
lean_ctor_set(v___x_2759_, 3, v___x_2757_);
lean_ctor_set(v___x_2759_, 4, v___x_2757_);
lean_ctor_set(v___x_2759_, 5, v___x_2757_);
lean_ctor_set(v___x_2759_, 6, v___x_2757_);
lean_ctor_set(v___x_2759_, 7, v___x_2757_);
lean_ctor_set(v___x_2759_, 8, v___x_2757_);
return v___x_2759_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = lean_unsigned_to_nat(32u);
v___x_2761_ = lean_mk_empty_array_with_capacity(v___x_2760_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2763_ = ((size_t)5ULL);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_unsigned_to_nat(32u);
v___x_2766_ = lean_mk_empty_array_with_capacity(v___x_2765_);
v___x_2767_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3);
v___x_2768_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v___x_2766_);
lean_ctor_set(v___x_2768_, 2, v___x_2764_);
lean_ctor_set(v___x_2768_, 3, v___x_2764_);
lean_ctor_set_usize(v___x_2768_, 4, v___x_2763_);
return v___x_2768_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = lean_box(1);
v___x_2770_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4);
v___x_2771_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
v___x_2772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v___x_2770_);
lean_ctor_set(v___x_2772_, 2, v___x_2769_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(lean_object* v_msgData_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; lean_object* v_env_2777_; lean_object* v___x_2778_; lean_object* v_scopes_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_opts_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2776_ = lean_st_ref_get(v___y_2774_);
v_env_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc_ref(v_env_2777_);
lean_dec(v___x_2776_);
v___x_2778_ = lean_st_ref_get(v___y_2774_);
v_scopes_2779_ = lean_ctor_get(v___x_2778_, 2);
lean_inc(v_scopes_2779_);
lean_dec(v___x_2778_);
v___x_2780_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2781_ = l_List_head_x21___redArg(v___x_2780_, v_scopes_2779_);
lean_dec(v_scopes_2779_);
v_opts_2782_ = lean_ctor_get(v___x_2781_, 1);
lean_inc_ref(v_opts_2782_);
lean_dec(v___x_2781_);
v___x_2783_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2);
v___x_2784_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5);
v___x_2785_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2785_, 0, v_env_2777_);
lean_ctor_set(v___x_2785_, 1, v___x_2783_);
lean_ctor_set(v___x_2785_, 2, v___x_2784_);
lean_ctor_set(v___x_2785_, 3, v_opts_2782_);
v___x_2786_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_msgData_2773_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_2788_, v___y_2789_);
lean_dec(v___y_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object* v_msg_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Elab_Command_getRef___redArg(v___y_2793_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v_macroStack_2798_; lean_object* v___x_2799_; lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2811_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v_macroStack_2798_ = lean_ctor_get(v___y_2793_, 4);
lean_inc(v_macroStack_2798_);
lean_dec_ref(v___y_2793_);
v___x_2799_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_2792_, v___y_2794_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
lean_inc(v_macroStack_2798_);
v___x_2801_ = l_Lean_Elab_getBetterRef(v_a_2797_, v_macroStack_2798_);
lean_dec(v_a_2797_);
v___x_2802_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_a_2800_, v_macroStack_2798_, v___y_2794_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2801_);
lean_ctor_set(v___x_2807_, 1, v_a_2803_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 1);
lean_ctor_set(v___x_2805_, 0, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v___y_2793_);
lean_dec_ref(v_msg_2792_);
v_a_2812_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2796_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2796_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object* v_msg_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object* v_ref_2825_, lean_object* v_msg_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Elab_Command_getRef___redArg(v___y_2827_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v_fileName_2832_; lean_object* v_fileMap_2833_; lean_object* v_currRecDepth_2834_; lean_object* v_cmdPos_2835_; lean_object* v_macroStack_2836_; lean_object* v_quotContext_x3f_2837_; lean_object* v_currMacroScope_2838_; lean_object* v_snap_x3f_2839_; lean_object* v_cancelTk_x3f_2840_; uint8_t v_suppressElabErrors_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2850_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v_fileName_2832_ = lean_ctor_get(v___y_2827_, 0);
v_fileMap_2833_ = lean_ctor_get(v___y_2827_, 1);
v_currRecDepth_2834_ = lean_ctor_get(v___y_2827_, 2);
v_cmdPos_2835_ = lean_ctor_get(v___y_2827_, 3);
v_macroStack_2836_ = lean_ctor_get(v___y_2827_, 4);
v_quotContext_x3f_2837_ = lean_ctor_get(v___y_2827_, 5);
v_currMacroScope_2838_ = lean_ctor_get(v___y_2827_, 6);
v_snap_x3f_2839_ = lean_ctor_get(v___y_2827_, 8);
v_cancelTk_x3f_2840_ = lean_ctor_get(v___y_2827_, 9);
v_suppressElabErrors_2841_ = lean_ctor_get_uint8(v___y_2827_, sizeof(void*)*10);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___y_2827_);
if (v_isSharedCheck_2850_ == 0)
{
lean_object* v_unused_2851_; 
v_unused_2851_ = lean_ctor_get(v___y_2827_, 7);
lean_dec(v_unused_2851_);
v___x_2843_ = v___y_2827_;
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_cancelTk_x3f_2840_);
lean_inc(v_snap_x3f_2839_);
lean_inc(v_currMacroScope_2838_);
lean_inc(v_quotContext_x3f_2837_);
lean_inc(v_macroStack_2836_);
lean_inc(v_cmdPos_2835_);
lean_inc(v_currRecDepth_2834_);
lean_inc(v_fileMap_2833_);
lean_inc(v_fileName_2832_);
lean_dec(v___y_2827_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_ref_2845_; lean_object* v___x_2847_; 
v_ref_2845_ = l_Lean_replaceRef(v_ref_2825_, v_a_2831_);
lean_dec(v_a_2831_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 7, v_ref_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_fileName_2832_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_fileMap_2833_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_currRecDepth_2834_);
lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_cmdPos_2835_);
lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_macroStack_2836_);
lean_ctor_set(v_reuseFailAlloc_2849_, 5, v_quotContext_x3f_2837_);
lean_ctor_set(v_reuseFailAlloc_2849_, 6, v_currMacroScope_2838_);
lean_ctor_set(v_reuseFailAlloc_2849_, 7, v_ref_2845_);
lean_ctor_set(v_reuseFailAlloc_2849_, 8, v_snap_x3f_2839_);
lean_ctor_set(v_reuseFailAlloc_2849_, 9, v_cancelTk_x3f_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2849_, sizeof(void*)*10, v_suppressElabErrors_2841_);
v___x_2847_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_2826_, v___x_2847_, v___y_2828_);
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v___y_2827_);
lean_dec_ref(v_msg_2826_);
v_a_2852_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2830_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2830_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object* v_ref_2860_, lean_object* v_msg_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_2860_, v_msg_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec(v_ref_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg(lean_object* v_cls_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v_scopes_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v_opts_2875_; uint8_t v_hasTrace_2876_; 
v___x_2869_ = l_Lean_inheritedTraceOptions;
v___x_2870_ = lean_st_ref_get(v___x_2869_);
v___x_2871_ = lean_st_ref_get(v___y_2867_);
v_scopes_2872_ = lean_ctor_get(v___x_2871_, 2);
lean_inc(v_scopes_2872_);
lean_dec(v___x_2871_);
v___x_2873_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2874_ = l_List_head_x21___redArg(v___x_2873_, v_scopes_2872_);
lean_dec(v_scopes_2872_);
v_opts_2875_ = lean_ctor_get(v___x_2874_, 1);
lean_inc_ref(v_opts_2875_);
lean_dec(v___x_2874_);
v_hasTrace_2876_ = lean_ctor_get_uint8(v_opts_2875_, sizeof(void*)*1);
if (v_hasTrace_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec_ref(v_opts_2875_);
lean_dec(v___x_2870_);
lean_dec(v_cls_2866_);
v___x_2877_ = lean_box(v_hasTrace_2876_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2879_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_2880_ = l_Lean_Name_append(v___x_2879_, v_cls_2866_);
v___x_2881_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2870_, v_opts_2875_, v___x_2880_);
lean_dec(v___x_2880_);
lean_dec_ref(v_opts_2875_);
lean_dec(v___x_2870_);
v___x_2882_ = lean_box(v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_cls_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg(v_cls_2884_, v___y_2885_);
lean_dec(v___y_2885_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(lean_object* v_cls_2888_, lean_object* v_msg_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Elab_Command_getRef___redArg(v___y_2890_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2942_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_2889_, v___y_2891_);
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2942_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2942_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v_traceState_2901_; lean_object* v_env_2902_; lean_object* v_messages_2903_; lean_object* v_scopes_2904_; lean_object* v_usedQuotCtxts_2905_; lean_object* v_nextMacroScope_2906_; lean_object* v_maxRecDepth_2907_; lean_object* v_ngen_2908_; lean_object* v_auxDeclNGen_2909_; lean_object* v_infoState_2910_; lean_object* v_snapshotTasks_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2941_; 
v___x_2900_ = lean_st_ref_take(v___y_2891_);
v_traceState_2901_ = lean_ctor_get(v___x_2900_, 9);
v_env_2902_ = lean_ctor_get(v___x_2900_, 0);
v_messages_2903_ = lean_ctor_get(v___x_2900_, 1);
v_scopes_2904_ = lean_ctor_get(v___x_2900_, 2);
v_usedQuotCtxts_2905_ = lean_ctor_get(v___x_2900_, 3);
v_nextMacroScope_2906_ = lean_ctor_get(v___x_2900_, 4);
v_maxRecDepth_2907_ = lean_ctor_get(v___x_2900_, 5);
v_ngen_2908_ = lean_ctor_get(v___x_2900_, 6);
v_auxDeclNGen_2909_ = lean_ctor_get(v___x_2900_, 7);
v_infoState_2910_ = lean_ctor_get(v___x_2900_, 8);
v_snapshotTasks_2911_ = lean_ctor_get(v___x_2900_, 10);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2913_ = v___x_2900_;
v_isShared_2914_ = v_isSharedCheck_2941_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_snapshotTasks_2911_);
lean_inc(v_traceState_2901_);
lean_inc(v_infoState_2910_);
lean_inc(v_auxDeclNGen_2909_);
lean_inc(v_ngen_2908_);
lean_inc(v_maxRecDepth_2907_);
lean_inc(v_nextMacroScope_2906_);
lean_inc(v_usedQuotCtxts_2905_);
lean_inc(v_scopes_2904_);
lean_inc(v_messages_2903_);
lean_inc(v_env_2902_);
lean_dec(v___x_2900_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2941_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint64_t v_tid_2915_; lean_object* v_traces_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2940_; 
v_tid_2915_ = lean_ctor_get_uint64(v_traceState_2901_, sizeof(void*)*1);
v_traces_2916_ = lean_ctor_get(v_traceState_2901_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_traceState_2901_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2918_ = v_traceState_2901_;
v_isShared_2919_ = v_isSharedCheck_2940_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_traces_2916_);
lean_dec(v_traceState_2901_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2940_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; double v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__0);
v___x_2922_ = 0;
v___x_2923_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1));
v___x_2924_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2924_, 0, v_cls_2888_);
lean_ctor_set(v___x_2924_, 1, v___x_2920_);
lean_ctor_set(v___x_2924_, 2, v___x_2923_);
lean_ctor_set_float(v___x_2924_, sizeof(void*)*3, v___x_2921_);
lean_ctor_set_float(v___x_2924_, sizeof(void*)*3 + 8, v___x_2921_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3 + 16, v___x_2922_);
v___x_2925_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__2));
v___x_2926_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v_a_2896_);
lean_ctor_set(v___x_2926_, 2, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v_a_2894_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = l_Lean_PersistentArray_push___redArg(v_traces_2916_, v___x_2927_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2928_);
v___x_2930_ = v___x_2918_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2928_);
lean_ctor_set_uint64(v_reuseFailAlloc_2939_, sizeof(void*)*1, v_tid_2915_);
v___x_2930_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2932_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 9, v___x_2930_);
v___x_2932_ = v___x_2913_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_env_2902_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_messages_2903_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_scopes_2904_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_usedQuotCtxts_2905_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_nextMacroScope_2906_);
lean_ctor_set(v_reuseFailAlloc_2938_, 5, v_maxRecDepth_2907_);
lean_ctor_set(v_reuseFailAlloc_2938_, 6, v_ngen_2908_);
lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_auxDeclNGen_2909_);
lean_ctor_set(v_reuseFailAlloc_2938_, 8, v_infoState_2910_);
lean_ctor_set(v_reuseFailAlloc_2938_, 9, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2938_, 10, v_snapshotTasks_2911_);
v___x_2932_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2933_ = lean_st_ref_set(v___y_2891_, v___x_2932_);
v___x_2934_ = lean_box(0);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2934_);
v___x_2936_ = v___x_2898_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_msg_2889_);
lean_dec(v_cls_2888_);
v_a_2943_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2893_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2893_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4___boxed(lean_object* v_cls_2951_, lean_object* v_msg_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_2951_, v_msg_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(lean_object* v_mod_2957_, uint8_t v_isMeta_2958_, lean_object* v_hint_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v_env_2964_; uint8_t v_isExporting_2965_; lean_object* v___x_2966_; lean_object* v_env_2967_; lean_object* v___x_2968_; lean_object* v_entry_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___y_2974_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2963_ = lean_st_ref_get(v___y_2961_);
v_env_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_ref(v_env_2964_);
lean_dec(v___x_2963_);
v_isExporting_2965_ = lean_ctor_get_uint8(v_env_2964_, sizeof(void*)*8);
lean_dec_ref(v_env_2964_);
v___x_2966_ = lean_st_ref_get(v___y_2961_);
v_env_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc_ref(v_env_2967_);
lean_dec(v___x_2966_);
v___x_2968_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__2);
lean_inc(v_mod_2957_);
v_entry_2969_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2969_, 0, v_mod_2957_);
lean_ctor_set_uint8(v_entry_2969_, sizeof(void*)*1, v_isExporting_2965_);
lean_ctor_set_uint8(v_entry_2969_, sizeof(void*)*1 + 1, v_isMeta_2958_);
v___x_2970_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2971_ = lean_box(1);
v___x_2972_ = lean_box(0);
v___x_3000_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2968_, v___x_2970_, v_env_2967_, v___x_2971_, v___x_2972_);
v___x_3001_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5_spec__16___redArg(v___x_3000_, v_entry_2969_);
if (v___x_3001_ == 0)
{
lean_object* v_cls_3002_; lean_object* v___x_3003_; lean_object* v_a_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3011_; lean_object* v___y_3012_; uint8_t v___x_3024_; 
v_cls_3002_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__8));
v___x_3003_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg(v_cls_3002_, v___y_2961_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3024_ = lean_unbox(v_a_3004_);
lean_dec(v_a_3004_);
if (v___x_3024_ == 0)
{
lean_dec(v_hint_2959_);
lean_dec(v_mod_2957_);
v___y_2974_ = v___y_2961_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_3025_; lean_object* v___y_3027_; 
v___x_3025_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__15);
if (v_isExporting_2965_ == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__20));
v___y_3027_ = v___x_3034_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__21));
v___y_3027_ = v___x_3035_;
goto v___jp_3026_;
}
v___jp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3028_ = l_Lean_stringToMessageData(v___y_3027_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3025_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__17);
v___x_3031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
if (v_isMeta_2958_ == 0)
{
lean_object* v___x_3032_; 
v___x_3032_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__18));
v___y_3011_ = v___x_3031_;
v___y_3012_ = v___x_3032_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3033_; 
v___x_3033_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__19));
v___y_3011_ = v___x_3031_;
v___y_3012_ = v___x_3033_;
goto v___jp_3010_;
}
}
}
v___jp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___y_3006_);
lean_ctor_set(v___x_3008_, 1, v___y_3007_);
v___x_3009_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_3002_, v___x_3008_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_dec_ref(v___x_3009_);
v___y_2974_ = v___y_2961_;
goto v___jp_2973_;
}
else
{
lean_dec_ref(v_entry_2969_);
return v___x_3009_;
}
}
v___jp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3013_ = l_Lean_stringToMessageData(v___y_3012_);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___y_3011_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__10);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_MessageData_ofName(v_mod_2957_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_Name_isAnonymous(v_hint_2959_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__12);
v___x_3021_ = l_Lean_MessageData_ofName(v_hint_2959_);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___y_3006_ = v___x_3018_;
v___y_3007_ = v___x_3022_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3023_; 
lean_dec(v_hint_2959_);
v___x_3023_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3_spec__5___closed__13);
v___y_3006_ = v___x_3018_;
v___y_3007_ = v___x_3023_;
goto v___jp_3005_;
}
}
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec_ref(v_entry_2969_);
lean_dec(v_hint_2959_);
lean_dec(v_mod_2957_);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
v___jp_2973_:
{
lean_object* v___x_2975_; lean_object* v_toEnvExtension_2976_; lean_object* v_env_2977_; lean_object* v_messages_2978_; lean_object* v_scopes_2979_; lean_object* v_usedQuotCtxts_2980_; lean_object* v_nextMacroScope_2981_; lean_object* v_maxRecDepth_2982_; lean_object* v_ngen_2983_; lean_object* v_auxDeclNGen_2984_; lean_object* v_infoState_2985_; lean_object* v_traceState_2986_; lean_object* v_snapshotTasks_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2999_; 
v___x_2975_ = lean_st_ref_take(v___y_2974_);
v_toEnvExtension_2976_ = lean_ctor_get(v___x_2970_, 0);
lean_inc_ref(v_toEnvExtension_2976_);
v_env_2977_ = lean_ctor_get(v___x_2975_, 0);
v_messages_2978_ = lean_ctor_get(v___x_2975_, 1);
v_scopes_2979_ = lean_ctor_get(v___x_2975_, 2);
v_usedQuotCtxts_2980_ = lean_ctor_get(v___x_2975_, 3);
v_nextMacroScope_2981_ = lean_ctor_get(v___x_2975_, 4);
v_maxRecDepth_2982_ = lean_ctor_get(v___x_2975_, 5);
v_ngen_2983_ = lean_ctor_get(v___x_2975_, 6);
v_auxDeclNGen_2984_ = lean_ctor_get(v___x_2975_, 7);
v_infoState_2985_ = lean_ctor_get(v___x_2975_, 8);
v_traceState_2986_ = lean_ctor_get(v___x_2975_, 9);
v_snapshotTasks_2987_ = lean_ctor_get(v___x_2975_, 10);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2989_ = v___x_2975_;
v_isShared_2990_ = v_isSharedCheck_2999_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_snapshotTasks_2987_);
lean_inc(v_traceState_2986_);
lean_inc(v_infoState_2985_);
lean_inc(v_auxDeclNGen_2984_);
lean_inc(v_ngen_2983_);
lean_inc(v_maxRecDepth_2982_);
lean_inc(v_nextMacroScope_2981_);
lean_inc(v_usedQuotCtxts_2980_);
lean_inc(v_scopes_2979_);
lean_inc(v_messages_2978_);
lean_inc(v_env_2977_);
lean_dec(v___x_2975_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2999_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_asyncMode_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v_asyncMode_2991_ = lean_ctor_get(v_toEnvExtension_2976_, 2);
lean_inc(v_asyncMode_2991_);
lean_dec_ref(v_toEnvExtension_2976_);
v___x_2992_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2970_, v_env_2977_, v_entry_2969_, v_asyncMode_2991_, v___x_2972_);
lean_dec(v_asyncMode_2991_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_messages_2978_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_scopes_2979_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_usedQuotCtxts_2980_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_nextMacroScope_2981_);
lean_ctor_set(v_reuseFailAlloc_2998_, 5, v_maxRecDepth_2982_);
lean_ctor_set(v_reuseFailAlloc_2998_, 6, v_ngen_2983_);
lean_ctor_set(v_reuseFailAlloc_2998_, 7, v_auxDeclNGen_2984_);
lean_ctor_set(v_reuseFailAlloc_2998_, 8, v_infoState_2985_);
lean_ctor_set(v_reuseFailAlloc_2998_, 9, v_traceState_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 10, v_snapshotTasks_2987_);
v___x_2994_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_st_ref_set(v___y_2974_, v___x_2994_);
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(lean_object* v_mod_3038_, lean_object* v_isMeta_3039_, lean_object* v_hint_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v_isMeta_boxed_3044_; lean_object* v_res_3045_; 
v_isMeta_boxed_3044_ = lean_unbox(v_isMeta_3039_);
v_res_3045_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_3038_, v_isMeta_boxed_3044_, v_hint_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(lean_object* v___x_3046_, lean_object* v_declName_3047_, lean_object* v_as_3048_, size_t v_sz_3049_, size_t v_i_3050_, lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
uint8_t v___x_3055_; 
v___x_3055_ = lean_usize_dec_lt(v_i_3050_, v_sz_3049_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v_declName_3047_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_b_3051_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; lean_object* v_modules_3058_; lean_object* v___x_3059_; lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v_toImport_3062_; lean_object* v_module_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3057_ = l_Lean_Environment_header(v___x_3046_);
v_modules_3058_ = lean_ctor_get(v___x_3057_, 3);
lean_inc_ref(v_modules_3058_);
lean_dec_ref(v___x_3057_);
v___x_3059_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3060_ = lean_array_uget_borrowed(v_as_3048_, v_i_3050_);
v___x_3061_ = lean_array_get(v___x_3059_, v_modules_3058_, v_a_3060_);
lean_dec_ref(v_modules_3058_);
v_toImport_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc_ref(v_toImport_3062_);
lean_dec(v___x_3061_);
v_module_3063_ = lean_ctor_get(v_toImport_3062_, 0);
lean_inc(v_module_3063_);
lean_dec_ref(v_toImport_3062_);
v___x_3064_ = 0;
lean_inc(v_declName_3047_);
v___x_3065_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3063_, v___x_3064_, v_declName_3047_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v___x_3066_; size_t v___x_3067_; size_t v___x_3068_; 
lean_dec_ref(v___x_3065_);
v___x_3066_ = lean_box(0);
v___x_3067_ = ((size_t)1ULL);
v___x_3068_ = lean_usize_add(v_i_3050_, v___x_3067_);
v_i_3050_ = v___x_3068_;
v_b_3051_ = v___x_3066_;
goto _start;
}
else
{
lean_dec(v_declName_3047_);
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(lean_object* v___x_3070_, lean_object* v_declName_3071_, lean_object* v_as_3072_, lean_object* v_sz_3073_, lean_object* v_i_3074_, lean_object* v_b_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
size_t v_sz_boxed_3079_; size_t v_i_boxed_3080_; lean_object* v_res_3081_; 
v_sz_boxed_3079_ = lean_unbox_usize(v_sz_3073_);
lean_dec(v_sz_3073_);
v_i_boxed_3080_ = lean_unbox_usize(v_i_3074_);
lean_dec(v_i_3074_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_3070_, v_declName_3071_, v_as_3072_, v_sz_boxed_3079_, v_i_boxed_3080_, v_b_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v_as_3072_);
lean_dec_ref(v___x_3070_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(lean_object* v_declName_3082_, uint8_t v_isMeta_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v_env_3091_; lean_object* v___y_3093_; lean_object* v___x_3106_; 
v___x_3087_ = lean_st_ref_get(v___y_3085_);
v_env_3091_ = lean_ctor_get(v___x_3087_, 0);
lean_inc_ref(v_env_3091_);
lean_dec(v___x_3087_);
v___x_3106_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3091_, v_declName_3082_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref(v_env_3091_);
lean_dec(v_declName_3082_);
goto v___jp_3088_;
}
else
{
lean_object* v_val_3107_; lean_object* v___x_3108_; lean_object* v_modules_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3107_);
lean_dec_ref(v___x_3106_);
v___x_3108_ = l_Lean_Environment_header(v_env_3091_);
v_modules_3109_ = lean_ctor_get(v___x_3108_, 3);
lean_inc_ref(v_modules_3109_);
lean_dec_ref(v___x_3108_);
v___x_3110_ = lean_array_get_size(v_modules_3109_);
v___x_3111_ = lean_nat_dec_lt(v_val_3107_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_dec_ref(v_modules_3109_);
lean_dec(v_val_3107_);
lean_dec_ref(v_env_3091_);
lean_dec(v_declName_3082_);
goto v___jp_3088_;
}
else
{
lean_object* v___x_3112_; lean_object* v_env_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___y_3117_; 
v___x_3112_ = lean_st_ref_get(v___y_3085_);
v_env_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_ref(v_env_3113_);
lean_dec(v___x_3112_);
v___x_3114_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__2);
v___x_3115_ = lean_array_fget(v_modules_3109_, v_val_3107_);
lean_dec(v_val_3107_);
lean_dec_ref(v_modules_3109_);
if (v_isMeta_3083_ == 0)
{
lean_dec_ref(v_env_3113_);
v___y_3117_ = v_isMeta_3083_;
goto v___jp_3116_;
}
else
{
uint8_t v___x_3128_; 
lean_inc(v_declName_3082_);
v___x_3128_ = l_Lean_isMarkedMeta(v_env_3113_, v_declName_3082_);
if (v___x_3128_ == 0)
{
v___y_3117_ = v_isMeta_3083_;
goto v___jp_3116_;
}
else
{
uint8_t v___x_3129_; 
v___x_3129_ = 0;
v___y_3117_ = v___x_3129_;
goto v___jp_3116_;
}
}
v___jp_3116_:
{
lean_object* v_toImport_3118_; lean_object* v_module_3119_; lean_object* v___x_3120_; 
v_toImport_3118_ = lean_ctor_get(v___x_3115_, 0);
lean_inc_ref(v_toImport_3118_);
lean_dec(v___x_3115_);
v_module_3119_ = lean_ctor_get(v_toImport_3118_, 0);
lean_inc(v_module_3119_);
lean_dec_ref(v_toImport_3118_);
lean_inc(v_declName_3082_);
v___x_3120_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3119_, v___y_3117_, v_declName_3082_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_dec_ref(v___x_3120_);
v___x_3121_ = l_Lean_indirectModUseExt;
v___x_3122_ = lean_box(1);
v___x_3123_ = lean_box(0);
lean_inc_ref(v_env_3091_);
v___x_3124_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3114_, v___x_3121_, v_env_3091_, v___x_3122_, v___x_3123_);
v___x_3125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_3124_, v_declName_3082_);
lean_dec(v___x_3124_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___closed__3));
v___y_3093_ = v___x_3126_;
goto v___jp_3092_;
}
else
{
lean_object* v_val_3127_; 
v_val_3127_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3127_);
lean_dec_ref(v___x_3125_);
v___y_3093_ = v_val_3127_;
goto v___jp_3092_;
}
}
else
{
lean_dec_ref(v_env_3091_);
lean_dec(v_declName_3082_);
return v___x_3120_;
}
}
}
}
v___jp_3088_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
v___jp_3092_:
{
lean_object* v___x_3094_; size_t v_sz_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_box(0);
v_sz_3095_ = lean_array_size(v___y_3093_);
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_3091_, v_declName_3082_, v___y_3093_, v_sz_3095_, v___x_3096_, v___x_3094_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v_env_3091_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; 
v_unused_3105_ = lean_ctor_get(v___x_3097_, 0);
lean_dec(v_unused_3105_);
v___x_3099_ = v___x_3097_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v___x_3097_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3094_);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3094_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
else
{
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(lean_object* v_declName_3130_, lean_object* v_isMeta_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v_isMeta_boxed_3135_; lean_object* v_res_3136_; 
v_isMeta_boxed_3135_ = lean_unbox(v_isMeta_3131_);
v_res_3136_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_3130_, v_isMeta_boxed_3135_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3136_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3));
v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
return v___x_3146_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5));
v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
return v___x_3149_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8(void){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7));
v___x_3152_ = l_Lean_stringToMessageData(v___x_3151_);
return v___x_3152_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9));
v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
return v___x_3155_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11));
v___x_3158_ = l_Lean_stringToMessageData(v___x_3157_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
v___x_3160_ = l_Lean_MessageData_note(v___x_3159_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14));
v___x_3163_ = l_Lean_stringToMessageData(v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_box(0);
v___x_3170_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17));
v___x_3171_ = l_Lean_mkConst(v___x_3170_, v___x_3169_);
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19));
v___x_3174_ = l_Lean_stringToMessageData(v___x_3173_);
return v___x_3174_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21));
v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* v_x_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
lean_inc(v_x_3178_);
v___x_3232_ = l_Lean_Syntax_isOfKind(v_x_3178_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref(v_a_3179_);
lean_dec(v_x_3178_);
v___x_3233_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = l_Lean_Syntax_getArg(v_x_3178_, v___x_3234_);
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3237_ = l_Lean_Syntax_matchesNull(v___x_3235_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
lean_dec_ref(v_a_3179_);
lean_dec(v_x_3178_);
v___x_3238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3238_;
}
else
{
lean_object* v___x_3239_; lean_object* v_id_3240_; lean_object* v___y_3242_; lean_object* v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___x_3280_; uint8_t v___x_3281_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; 
v___x_3239_ = lean_unsigned_to_nat(2u);
v_id_3240_ = l_Lean_Syntax_getArg(v_x_3178_, v___x_3239_);
v___x_3280_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54));
lean_inc(v_id_3240_);
v___x_3281_ = l_Lean_Syntax_isOfKind(v_id_3240_, v___x_3280_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3309_; 
lean_dec(v_id_3240_);
lean_dec_ref(v_a_3179_);
lean_dec(v_x_3178_);
v___x_3309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3309_;
}
else
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Elab_Command_getRef___redArg(v_a_3179_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; lean_object* v_fileName_3313_; lean_object* v_fileMap_3314_; lean_object* v_currRecDepth_3315_; lean_object* v_cmdPos_3316_; lean_object* v_macroStack_3317_; lean_object* v_quotContext_x3f_3318_; lean_object* v_currMacroScope_3319_; lean_object* v_snap_x3f_3320_; lean_object* v_cancelTk_x3f_3321_; uint8_t v_suppressElabErrors_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3363_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = lean_st_ref_get(v_a_3180_);
v_fileName_3313_ = lean_ctor_get(v_a_3179_, 0);
v_fileMap_3314_ = lean_ctor_get(v_a_3179_, 1);
v_currRecDepth_3315_ = lean_ctor_get(v_a_3179_, 2);
v_cmdPos_3316_ = lean_ctor_get(v_a_3179_, 3);
v_macroStack_3317_ = lean_ctor_get(v_a_3179_, 4);
v_quotContext_x3f_3318_ = lean_ctor_get(v_a_3179_, 5);
v_currMacroScope_3319_ = lean_ctor_get(v_a_3179_, 6);
v_snap_x3f_3320_ = lean_ctor_get(v_a_3179_, 8);
v_cancelTk_x3f_3321_ = lean_ctor_get(v_a_3179_, 9);
v_suppressElabErrors_3322_ = lean_ctor_get_uint8(v_a_3179_, sizeof(void*)*10);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_a_3179_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v_a_3179_, 7);
lean_dec(v_unused_3364_);
v___x_3324_ = v_a_3179_;
v_isShared_3325_ = v_isSharedCheck_3363_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_cancelTk_x3f_3321_);
lean_inc(v_snap_x3f_3320_);
lean_inc(v_currMacroScope_3319_);
lean_inc(v_quotContext_x3f_3318_);
lean_inc(v_macroStack_3317_);
lean_inc(v_cmdPos_3316_);
lean_inc(v_currRecDepth_3315_);
lean_inc(v_fileMap_3314_);
lean_inc(v_fileName_3313_);
lean_dec(v_a_3179_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3363_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_env_3326_; lean_object* v_cmd_3327_; lean_object* v___x_3328_; lean_object* v_t_3329_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v_ref_3355_; lean_object* v___x_3357_; 
v_env_3326_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_ref(v_env_3326_);
lean_dec(v___x_3312_);
v_cmd_3327_ = l_Lean_Syntax_getArg(v_x_3178_, v___x_3236_);
v___x_3328_ = lean_unsigned_to_nat(3u);
v_t_3329_ = l_Lean_Syntax_getArg(v_x_3178_, v___x_3328_);
lean_dec(v_x_3178_);
v_ref_3355_ = l_Lean_replaceRef(v_cmd_3327_, v_a_3311_);
lean_dec(v_a_3311_);
lean_dec(v_cmd_3327_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 7, v_ref_3355_);
v___x_3357_ = v___x_3324_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_fileName_3313_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_fileMap_3314_);
lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_currRecDepth_3315_);
lean_ctor_set(v_reuseFailAlloc_3362_, 3, v_cmdPos_3316_);
lean_ctor_set(v_reuseFailAlloc_3362_, 4, v_macroStack_3317_);
lean_ctor_set(v_reuseFailAlloc_3362_, 5, v_quotContext_x3f_3318_);
lean_ctor_set(v_reuseFailAlloc_3362_, 6, v_currMacroScope_3319_);
lean_ctor_set(v_reuseFailAlloc_3362_, 7, v_ref_3355_);
lean_ctor_set(v_reuseFailAlloc_3362_, 8, v_snap_x3f_3320_);
lean_ctor_set(v_reuseFailAlloc_3362_, 9, v_cancelTk_x3f_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3362_, sizeof(void*)*10, v_suppressElabErrors_3322_);
v___x_3357_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3356_;
}
v___jp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17));
v___x_3334_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_3333_, v___x_3281_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; 
lean_dec_ref(v___x_3334_);
v___x_3335_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18);
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3336_, 0, v_t_3329_);
lean_closure_set(v___f_3336_, 1, v___x_3335_);
lean_inc_ref(v___y_3331_);
v___x_3337_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3336_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = l_Lean_TSyntax_getId(v_id_3240_);
v___x_3340_ = l_Lean_Name_isAnonymous(v___x_3339_);
if (v___x_3340_ == 0)
{
v___y_3298_ = v___x_3339_;
v___y_3299_ = v_a_3338_;
v___y_3300_ = v___y_3331_;
v___y_3301_ = v___y_3332_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec(v___x_3339_);
lean_dec(v_a_3338_);
v___x_3341_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20);
lean_inc(v_id_3240_);
v___x_3342_ = l_Lean_MessageData_ofSyntax(v_id_3240_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3240_, v___x_3345_, v___y_3331_, v___y_3332_);
lean_dec(v_id_3240_);
return v___x_3346_;
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___y_3331_);
lean_dec(v_id_3240_);
v_a_3347_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3337_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3337_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
else
{
lean_dec_ref(v___y_3331_);
lean_dec(v_t_3329_);
lean_dec(v_id_3240_);
return v___x_3334_;
}
}
v_reusejp_3356_:
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17));
v___x_3359_ = l_Lean_Environment_contains(v_env_3326_, v___x_3358_, v___x_3281_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec(v_t_3329_);
lean_dec(v_id_3240_);
v___x_3360_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22);
v___x_3361_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v___x_3360_, v___x_3357_, v_a_3180_);
return v___x_3361_;
}
else
{
v___y_3331_ = v___x_3357_;
v___y_3332_ = v_a_3180_;
goto v___jp_3330_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_id_3240_);
lean_dec_ref(v_a_3179_);
lean_dec(v_x_3178_);
v_a_3365_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3310_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3310_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
v___jp_3241_:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Syntax_getTailPos_x3f(v_id_3240_, v___y_3244_);
lean_dec(v_id_3240_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_inc(v___y_3248_);
v___y_3183_ = v___y_3242_;
v___y_3184_ = v___y_3248_;
v___y_3185_ = v___y_3243_;
v___y_3186_ = v___y_3245_;
v___y_3187_ = v___y_3246_;
v___y_3188_ = v___y_3247_;
v___y_3189_ = v___y_3248_;
goto v___jp_3182_;
}
else
{
lean_object* v_val_3250_; 
v_val_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3250_);
lean_dec_ref(v___x_3249_);
v___y_3183_ = v___y_3242_;
v___y_3184_ = v___y_3248_;
v___y_3185_ = v___y_3243_;
v___y_3186_ = v___y_3245_;
v___y_3187_ = v___y_3246_;
v___y_3188_ = v___y_3247_;
v___y_3189_ = v_val_3250_;
goto v___jp_3182_;
}
}
v___jp_3251_:
{
lean_object* v_fileMap_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; 
v_fileMap_3256_ = lean_ctor_get(v___y_3254_, 1);
lean_inc_ref(v_fileMap_3256_);
v___x_3257_ = 0;
v___x_3258_ = l_Lean_Syntax_getPos_x3f(v_id_3240_, v___x_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
v___y_3242_ = v___y_3252_;
v___y_3243_ = v_fileMap_3256_;
v___y_3244_ = v___x_3257_;
v___y_3245_ = v___y_3255_;
v___y_3246_ = v___y_3253_;
v___y_3247_ = v___y_3254_;
v___y_3248_ = v___x_3234_;
goto v___jp_3241_;
}
else
{
lean_object* v_val_3259_; 
v_val_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_val_3259_);
lean_dec_ref(v___x_3258_);
v___y_3242_ = v___y_3252_;
v___y_3243_ = v_fileMap_3256_;
v___y_3244_ = v___x_3257_;
v___y_3245_ = v___y_3255_;
v___y_3246_ = v___y_3253_;
v___y_3247_ = v___y_3254_;
v___y_3248_ = v_val_3259_;
goto v___jp_3241_;
}
}
v___jp_3260_:
{
lean_object* v___x_3265_; lean_object* v_env_3266_; lean_object* v___x_3267_; lean_object* v_toEnvExtension_3268_; lean_object* v_asyncMode_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3265_ = lean_st_ref_get(v___y_3264_);
v_env_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc_ref(v_env_3266_);
lean_dec(v___x_3265_);
v___x_3267_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc_ref(v_toEnvExtension_3268_);
v_asyncMode_3269_ = lean_ctor_get(v_toEnvExtension_3268_, 2);
lean_inc(v_asyncMode_3269_);
lean_dec_ref(v_toEnvExtension_3268_);
v___x_3270_ = lean_box(1);
v___x_3271_ = lean_box(0);
v___x_3272_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3270_, v___x_3267_, v_env_3266_, v_asyncMode_3269_, v___x_3271_);
lean_dec(v_asyncMode_3269_);
v___x_3273_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_3261_, v___x_3272_);
lean_dec(v___x_3272_);
if (v___x_3273_ == 0)
{
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___y_3263_;
v___y_3255_ = v___y_3264_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec_ref(v___y_3262_);
v___x_3274_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
v___x_3275_ = l_Lean_MessageData_ofName(v___y_3261_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3240_, v___x_3278_, v___y_3263_, v___y_3264_);
lean_dec(v_id_3240_);
return v___x_3279_;
}
}
v___jp_3282_:
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = l_Lean_Name_getNumParts(v___y_3283_);
v___x_3288_ = lean_nat_dec_eq(v___x_3287_, v___x_3239_);
lean_dec(v___x_3287_);
if (v___x_3288_ == 0)
{
if (v___x_3281_ == 0)
{
v___y_3261_ = v___y_3283_;
v___y_3262_ = v___y_3284_;
v___y_3263_ = v___y_3285_;
v___y_3264_ = v___y_3286_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec_ref(v___y_3284_);
v___x_3289_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8);
v___x_3290_ = l_Lean_MessageData_ofName(v___y_3283_);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3240_, v___x_3295_, v___y_3285_, v___y_3286_);
lean_dec(v_id_3240_);
return v___x_3296_;
}
}
else
{
v___y_3261_ = v___y_3283_;
v___y_3262_ = v___y_3284_;
v___y_3263_ = v___y_3285_;
v___y_3264_ = v___y_3286_;
goto v___jp_3260_;
}
}
v___jp_3297_:
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_Name_hasMacroScopes(v___y_3298_);
if (v___x_3302_ == 0)
{
v___y_3283_ = v___y_3298_;
v___y_3284_ = v___y_3299_;
v___y_3285_ = v___y_3300_;
v___y_3286_ = v___y_3301_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
v___x_3303_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8);
lean_inc(v_id_3240_);
v___x_3304_ = l_Lean_MessageData_ofSyntax(v_id_3240_);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3240_, v___x_3307_, v___y_3300_, v___y_3301_);
lean_dec(v_id_3240_);
return v___x_3308_;
}
}
}
}
v___jp_3182_:
{
lean_object* v___x_3190_; lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v___y_3188_);
v___x_3190_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_3186_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3230_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3230_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v_env_3196_; lean_object* v_messages_3197_; lean_object* v_scopes_3198_; lean_object* v_usedQuotCtxts_3199_; lean_object* v_nextMacroScope_3200_; lean_object* v_maxRecDepth_3201_; lean_object* v_ngen_3202_; lean_object* v_auxDeclNGen_3203_; lean_object* v_infoState_3204_; lean_object* v_traceState_3205_; lean_object* v_snapshotTasks_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3229_; 
v___x_3195_ = lean_st_ref_take(v___y_3186_);
v_env_3196_ = lean_ctor_get(v___x_3195_, 0);
v_messages_3197_ = lean_ctor_get(v___x_3195_, 1);
v_scopes_3198_ = lean_ctor_get(v___x_3195_, 2);
v_usedQuotCtxts_3199_ = lean_ctor_get(v___x_3195_, 3);
v_nextMacroScope_3200_ = lean_ctor_get(v___x_3195_, 4);
v_maxRecDepth_3201_ = lean_ctor_get(v___x_3195_, 5);
v_ngen_3202_ = lean_ctor_get(v___x_3195_, 6);
v_auxDeclNGen_3203_ = lean_ctor_get(v___x_3195_, 7);
v_infoState_3204_ = lean_ctor_get(v___x_3195_, 8);
v_traceState_3205_ = lean_ctor_get(v___x_3195_, 9);
v_snapshotTasks_3206_ = lean_ctor_get(v___x_3195_, 10);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3208_ = v___x_3195_;
v_isShared_3209_ = v_isSharedCheck_3229_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_snapshotTasks_3206_);
lean_inc(v_traceState_3205_);
lean_inc(v_infoState_3204_);
lean_inc(v_auxDeclNGen_3203_);
lean_inc(v_ngen_3202_);
lean_inc(v_maxRecDepth_3201_);
lean_inc(v_nextMacroScope_3200_);
lean_inc(v_usedQuotCtxts_3199_);
lean_inc(v_scopes_3198_);
lean_inc(v_messages_3197_);
lean_inc(v_env_3196_);
lean_dec(v___x_3195_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3229_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v_toEnvExtension_3211_; lean_object* v_asyncMode_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3210_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc_ref(v_toEnvExtension_3211_);
v_asyncMode_3212_ = lean_ctor_get(v_toEnvExtension_3211_, 2);
lean_inc(v_asyncMode_3212_);
lean_dec_ref(v_toEnvExtension_3211_);
v___x_3213_ = l_Lean_DeclarationRange_ofStringPositions(v___y_3185_, v___y_3184_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec(v___y_3184_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_a_3191_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___closed__1));
v___x_3217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v___y_3187_);
lean_ctor_set(v___x_3217_, 2, v___x_3215_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___y_3183_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_box(0);
v___x_3220_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3210_, v_env_3196_, v___x_3218_, v_asyncMode_3212_, v___x_3219_);
lean_dec(v_asyncMode_3212_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3220_);
v___x_3222_ = v___x_3208_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_messages_3197_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_scopes_3198_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_usedQuotCtxts_3199_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_nextMacroScope_3200_);
lean_ctor_set(v_reuseFailAlloc_3228_, 5, v_maxRecDepth_3201_);
lean_ctor_set(v_reuseFailAlloc_3228_, 6, v_ngen_3202_);
lean_ctor_set(v_reuseFailAlloc_3228_, 7, v_auxDeclNGen_3203_);
lean_ctor_set(v_reuseFailAlloc_3228_, 8, v_infoState_3204_);
lean_ctor_set(v_reuseFailAlloc_3228_, 9, v_traceState_3205_);
lean_ctor_set(v_reuseFailAlloc_3228_, 10, v_snapshotTasks_3206_);
v___x_3222_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3223_ = lean_st_ref_set(v___y_3186_, v___x_3222_);
v___x_3224_ = lean_box(0);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3224_);
v___x_3226_ = v___x_3193_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object* v_x_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_3373_, v_a_3374_, v_a_3375_);
lean_dec(v_a_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object* v_00_u03b1_3378_, lean_object* v_ref_3379_, lean_object* v_msg_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_3379_, v_msg_3380_, v___y_3381_, v___y_3382_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object* v_00_u03b1_3385_, lean_object* v_ref_3386_, lean_object* v_msg_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v_00_u03b1_3385_, v_ref_3386_, v_msg_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec(v_ref_3386_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(lean_object* v_msgData_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_3392_, v___y_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(lean_object* v_msgData_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(v_msgData_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object* v_00_u03b1_3402_, lean_object* v_msg_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_3403_, v___y_3404_, v___y_3405_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object* v_00_u03b1_3408_, lean_object* v_msg_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(v_00_u03b1_3408_, v_msg_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(lean_object* v_cls_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___redArg(v_cls_3414_, v___y_3416_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___boxed(lean_object* v_cls_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(lean_object* v_msgData_3424_, lean_object* v_macroStack_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_3424_, v_macroStack_3425_, v___y_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(lean_object* v_msgData_3430_, lean_object* v_macroStack_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(v_msgData_3430_, v_macroStack_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3443_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3444_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
v___x_3445_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1));
v___x_3446_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
v___x_3447_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3443_, v___x_3444_, v___x_3445_, v___x_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
return v_res_3449_;
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
res = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap);
res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
