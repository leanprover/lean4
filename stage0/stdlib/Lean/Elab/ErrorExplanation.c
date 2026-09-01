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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
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
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.logNamedWarningAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "logNamedWarningAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value),LEAN_SCALAR_PTR_LITERAL(165, 244, 38, 255, 142, 163, 212, 242)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
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
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__5;
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
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19));
v___x_63_ = l_String_toRawSubstring_x27(v___x_62_);
return v___x_63_;
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
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_id_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = l_Lean_Syntax_getArg(v_x_156_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(2u);
v_id_180_ = l_Lean_Syntax_getArg(v_x_156_, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(4u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_156_, v___x_181_);
lean_dec(v_x_156_);
if (v___x_168_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc(v___x_182_);
v___x_224_ = l_Lean_Syntax_isOfKind(v___x_182_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v_quotContext_225_; lean_object* v_currMacroScope_226_; lean_object* v_ref_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___y_238_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_quotContext_225_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_226_ = lean_ctor_get(v_a_157_, 2);
v_ref_227_ = lean_ctor_get(v_a_157_, 5);
v___x_228_ = l_Lean_SourceInfo_fromRef(v_ref_227_, v___x_168_);
v___x_229_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_230_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20);
v___x_231_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22));
lean_inc(v_currMacroScope_226_);
lean_inc(v_quotContext_225_);
v___x_232_ = l_Lean_addMacroScope(v_quotContext_225_, v___x_231_, v_currMacroScope_226_);
v___x_233_ = lean_box(0);
v___x_234_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24));
lean_inc(v___x_228_);
v___x_235_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_235_, 0, v___x_228_);
lean_ctor_set(v___x_235_, 1, v___x_230_);
lean_ctor_set(v___x_235_, 2, v___x_232_);
lean_ctor_set(v___x_235_, 3, v___x_234_);
v___x_236_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_242_ = l_Lean_TSyntax_getId(v_id_180_);
lean_dec(v_id_180_);
lean_inc(v___x_242_);
v___x_243_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_233_, v___x_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_quoteNameMk(v___x_242_);
v___y_238_ = v___x_244_;
goto v___jp_237_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_242_);
v_val_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v___x_243_, 1);
v___x_246_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_247_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_248_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_249_ = lean_string_intercalate(v___x_248_, v_val_245_);
v___x_250_ = lean_string_append(v___x_247_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = lean_box(2);
v___x_252_ = l_Lean_Syntax_mkNameLit(v___x_250_, v___x_251_);
v___x_253_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_254_ = lean_array_push(v___x_253_, v___x_252_);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v___x_251_);
lean_ctor_set(v___x_255_, 1, v___x_246_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
v___y_238_ = v___x_255_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_inc(v___x_228_);
v___x_239_ = l_Lean_Syntax_node3(v___x_228_, v___x_236_, v___x_178_, v___y_238_, v___x_182_);
v___x_240_ = l_Lean_Syntax_node2(v___x_228_, v___x_229_, v___x_235_, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_a_158_);
return v___x_241_;
}
}
else
{
goto v___jp_196_;
}
}
else
{
goto v___jp_196_;
}
v___jp_183_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_189_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
v___x_190_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16));
lean_inc_n(v___y_186_, 3);
v___x_191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_191_, 0, v___y_186_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = l_Lean_Syntax_node2(v___y_186_, v___x_189_, v___x_191_, v___x_182_);
lean_inc(v___y_187_);
v___x_193_ = l_Lean_Syntax_node3(v___y_186_, v___y_187_, v___x_178_, v___y_188_, v___x_192_);
lean_inc(v___y_184_);
v___x_194_ = l_Lean_Syntax_node2(v___y_186_, v___y_184_, v___y_185_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_158_);
return v___x_195_;
}
v___jp_196_:
{
lean_object* v_quotContext_197_; lean_object* v_currMacroScope_198_; lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_quotContext_197_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_198_ = lean_ctor_get(v_a_157_, 2);
v_ref_199_ = lean_ctor_get(v_a_157_, 5);
v___x_200_ = l_Lean_SourceInfo_fromRef(v_ref_199_, v___x_168_);
v___x_201_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_202_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20);
v___x_203_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22));
lean_inc(v_currMacroScope_198_);
lean_inc(v_quotContext_197_);
v___x_204_ = l_Lean_addMacroScope(v_quotContext_197_, v___x_203_, v_currMacroScope_198_);
v___x_205_ = lean_box(0);
v___x_206_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24));
lean_inc(v___x_200_);
v___x_207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_207_, 0, v___x_200_);
lean_ctor_set(v___x_207_, 1, v___x_202_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
lean_ctor_set(v___x_207_, 3, v___x_206_);
v___x_208_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_209_ = l_Lean_TSyntax_getId(v_id_180_);
lean_dec(v_id_180_);
lean_inc(v___x_209_);
v___x_210_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_205_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_quoteNameMk(v___x_209_);
v___y_184_ = v___x_201_;
v___y_185_ = v___x_207_;
v___y_186_ = v___x_200_;
v___y_187_ = v___x_208_;
v___y_188_ = v___x_211_;
goto v___jp_183_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v___x_209_);
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___x_213_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_214_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_215_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_216_ = lean_string_intercalate(v___x_215_, v_val_212_);
v___x_217_ = lean_string_append(v___x_214_, v___x_216_);
lean_dec_ref(v___x_216_);
v___x_218_ = lean_box(2);
v___x_219_ = l_Lean_Syntax_mkNameLit(v___x_217_, v___x_218_);
v___x_220_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_221_ = lean_array_push(v___x_220_, v___x_219_);
v___x_222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_222_, 0, v___x_218_);
lean_ctor_set(v___x_222_, 1, v___x_213_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
v___y_184_ = v___x_201_;
v___y_185_ = v___x_207_;
v___y_186_ = v___x_200_;
v___y_187_ = v___x_208_;
v___y_188_ = v___x_222_;
goto v___jp_183_;
}
}
}
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_unsigned_to_nat(2u);
v___x_258_ = l_Lean_Syntax_getArg(v_x_156_, v___x_257_);
v___x_259_ = l_Lean_Syntax_matchesNull(v___x_258_, v___x_256_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_x_156_);
v___x_260_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v_id_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v_id_262_ = l_Lean_Syntax_getArg(v_x_156_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(3u);
v___x_264_ = l_Lean_Syntax_getArg(v_x_156_, v___x_263_);
lean_dec(v_x_156_);
if (v___x_166_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc(v___x_264_);
v___x_306_ = l_Lean_Syntax_isOfKind(v___x_264_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v_quotContext_307_; lean_object* v_currMacroScope_308_; lean_object* v_ref_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___y_320_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_quotContext_307_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_308_ = lean_ctor_get(v_a_157_, 2);
v_ref_309_ = lean_ctor_get(v_a_157_, 5);
v___x_310_ = l_Lean_SourceInfo_fromRef(v_ref_309_, v___x_166_);
v___x_311_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_312_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
v___x_313_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36));
lean_inc(v_currMacroScope_308_);
lean_inc(v_quotContext_307_);
v___x_314_ = l_Lean_addMacroScope(v_quotContext_307_, v___x_313_, v_currMacroScope_308_);
v___x_315_ = lean_box(0);
v___x_316_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38));
lean_inc(v___x_310_);
v___x_317_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_317_, 0, v___x_310_);
lean_ctor_set(v___x_317_, 1, v___x_312_);
lean_ctor_set(v___x_317_, 2, v___x_314_);
lean_ctor_set(v___x_317_, 3, v___x_316_);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_324_ = l_Lean_TSyntax_getId(v_id_262_);
lean_dec(v_id_262_);
lean_inc(v___x_324_);
v___x_325_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_315_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_quoteNameMk(v___x_324_);
v___y_320_ = v___x_326_;
goto v___jp_319_;
}
else
{
lean_object* v_val_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v___x_324_);
v_val_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_325_, 1);
v___x_328_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_329_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_330_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_331_ = lean_string_intercalate(v___x_330_, v_val_327_);
v___x_332_ = lean_string_append(v___x_329_, v___x_331_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_box(2);
v___x_334_ = l_Lean_Syntax_mkNameLit(v___x_332_, v___x_333_);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_261_);
v___x_336_ = lean_array_push(v___x_335_, v___x_334_);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___x_333_);
lean_ctor_set(v___x_337_, 1, v___x_328_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___y_320_ = v___x_337_;
goto v___jp_319_;
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_inc(v___x_310_);
v___x_321_ = l_Lean_Syntax_node2(v___x_310_, v___x_318_, v___y_320_, v___x_264_);
v___x_322_ = l_Lean_Syntax_node2(v___x_310_, v___x_311_, v___x_317_, v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_158_);
return v___x_323_;
}
}
else
{
goto v___jp_278_;
}
}
else
{
goto v___jp_278_;
}
v___jp_265_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_271_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
v___x_272_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16));
lean_inc_n(v___y_266_, 3);
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___y_266_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = l_Lean_Syntax_node2(v___y_266_, v___x_271_, v___x_273_, v___x_264_);
lean_inc(v___y_269_);
v___x_275_ = l_Lean_Syntax_node2(v___y_266_, v___y_269_, v___y_270_, v___x_274_);
lean_inc(v___y_267_);
v___x_276_ = l_Lean_Syntax_node2(v___y_266_, v___y_267_, v___y_268_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_a_158_);
return v___x_277_;
}
v___jp_278_:
{
lean_object* v_quotContext_279_; lean_object* v_currMacroScope_280_; lean_object* v_ref_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_quotContext_279_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_280_ = lean_ctor_get(v_a_157_, 2);
v_ref_281_ = lean_ctor_get(v_a_157_, 5);
v___x_282_ = l_Lean_SourceInfo_fromRef(v_ref_281_, v___x_166_);
v___x_283_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_284_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
v___x_285_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36));
lean_inc(v_currMacroScope_280_);
lean_inc(v_quotContext_279_);
v___x_286_ = l_Lean_addMacroScope(v_quotContext_279_, v___x_285_, v_currMacroScope_280_);
v___x_287_ = lean_box(0);
v___x_288_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38));
lean_inc(v___x_282_);
v___x_289_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_289_, 0, v___x_282_);
lean_ctor_set(v___x_289_, 1, v___x_284_);
lean_ctor_set(v___x_289_, 2, v___x_286_);
lean_ctor_set(v___x_289_, 3, v___x_288_);
v___x_290_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_291_ = l_Lean_TSyntax_getId(v_id_262_);
lean_dec(v_id_262_);
lean_inc(v___x_291_);
v___x_292_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_287_, v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_quoteNameMk(v___x_291_);
v___y_266_ = v___x_282_;
v___y_267_ = v___x_283_;
v___y_268_ = v___x_289_;
v___y_269_ = v___x_290_;
v___y_270_ = v___x_293_;
goto v___jp_265_;
}
else
{
lean_object* v_val_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v___x_291_);
v_val_294_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___x_292_, 1);
v___x_295_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_296_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_297_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_298_ = lean_string_intercalate(v___x_297_, v_val_294_);
v___x_299_ = lean_string_append(v___x_296_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_box(2);
v___x_301_ = l_Lean_Syntax_mkNameLit(v___x_299_, v___x_300_);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_261_);
v___x_303_ = lean_array_push(v___x_302_, v___x_301_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_300_);
lean_ctor_set(v___x_304_, 1, v___x_295_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
v___y_266_ = v___x_282_;
v___y_267_ = v___x_283_;
v___y_268_ = v___x_289_;
v___y_269_ = v___x_290_;
v___y_270_ = v___x_304_;
goto v___jp_265_;
}
}
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_unsigned_to_nat(3u);
v___x_340_ = l_Lean_Syntax_getArg(v_x_156_, v___x_339_);
v___x_341_ = l_Lean_Syntax_matchesNull(v___x_340_, v___x_338_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_dec(v_x_156_);
v___x_342_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_342_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_id_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = l_Lean_Syntax_getArg(v_x_156_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(2u);
v_id_346_ = l_Lean_Syntax_getArg(v_x_156_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(4u);
v___x_348_ = l_Lean_Syntax_getArg(v_x_156_, v___x_347_);
lean_dec(v_x_156_);
if (v___x_164_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc(v___x_348_);
v___x_390_ = l_Lean_Syntax_isOfKind(v___x_348_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v_quotContext_391_; lean_object* v_currMacroScope_392_; lean_object* v_ref_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___y_404_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_quotContext_391_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_392_ = lean_ctor_get(v_a_157_, 2);
v_ref_393_ = lean_ctor_get(v_a_157_, 5);
v___x_394_ = l_Lean_SourceInfo_fromRef(v_ref_393_, v___x_164_);
v___x_395_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_396_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
v___x_397_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42));
lean_inc(v_currMacroScope_392_);
lean_inc(v_quotContext_391_);
v___x_398_ = l_Lean_addMacroScope(v_quotContext_391_, v___x_397_, v_currMacroScope_392_);
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44));
lean_inc(v___x_394_);
v___x_401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_401_, 0, v___x_394_);
lean_ctor_set(v___x_401_, 1, v___x_396_);
lean_ctor_set(v___x_401_, 2, v___x_398_);
lean_ctor_set(v___x_401_, 3, v___x_400_);
v___x_402_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_408_ = l_Lean_TSyntax_getId(v_id_346_);
lean_dec(v_id_346_);
lean_inc(v___x_408_);
v___x_409_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_399_, v___x_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_quoteNameMk(v___x_408_);
v___y_404_ = v___x_410_;
goto v___jp_403_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v___x_408_);
v_val_411_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_409_, 1);
v___x_412_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_413_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_414_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_415_ = lean_string_intercalate(v___x_414_, v_val_411_);
v___x_416_ = lean_string_append(v___x_413_, v___x_415_);
lean_dec_ref(v___x_415_);
v___x_417_ = lean_box(2);
v___x_418_ = l_Lean_Syntax_mkNameLit(v___x_416_, v___x_417_);
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_420_ = lean_array_push(v___x_419_, v___x_418_);
v___x_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_417_);
lean_ctor_set(v___x_421_, 1, v___x_412_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
v___y_404_ = v___x_421_;
goto v___jp_403_;
}
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc(v___x_394_);
v___x_405_ = l_Lean_Syntax_node3(v___x_394_, v___x_402_, v___x_344_, v___y_404_, v___x_348_);
v___x_406_ = l_Lean_Syntax_node2(v___x_394_, v___x_395_, v___x_401_, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_158_);
return v___x_407_;
}
}
else
{
goto v___jp_362_;
}
}
else
{
goto v___jp_362_;
}
v___jp_349_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_355_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
v___x_356_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16));
lean_inc_n(v___y_353_, 3);
v___x_357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_357_, 0, v___y_353_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_Syntax_node2(v___y_353_, v___x_355_, v___x_357_, v___x_348_);
lean_inc(v___y_351_);
v___x_359_ = l_Lean_Syntax_node3(v___y_353_, v___y_351_, v___x_344_, v___y_354_, v___x_358_);
lean_inc(v___y_350_);
v___x_360_ = l_Lean_Syntax_node2(v___y_353_, v___y_350_, v___y_352_, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_158_);
return v___x_361_;
}
v___jp_362_:
{
lean_object* v_quotContext_363_; lean_object* v_currMacroScope_364_; lean_object* v_ref_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_quotContext_363_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_364_ = lean_ctor_get(v_a_157_, 2);
v_ref_365_ = lean_ctor_get(v_a_157_, 5);
v___x_366_ = l_Lean_SourceInfo_fromRef(v_ref_365_, v___x_164_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_368_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
v___x_369_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42));
lean_inc(v_currMacroScope_364_);
lean_inc(v_quotContext_363_);
v___x_370_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_369_, v_currMacroScope_364_);
v___x_371_ = lean_box(0);
v___x_372_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44));
lean_inc(v___x_366_);
v___x_373_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_373_, 0, v___x_366_);
lean_ctor_set(v___x_373_, 1, v___x_368_);
lean_ctor_set(v___x_373_, 2, v___x_370_);
lean_ctor_set(v___x_373_, 3, v___x_372_);
v___x_374_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_375_ = l_Lean_TSyntax_getId(v_id_346_);
lean_dec(v_id_346_);
lean_inc(v___x_375_);
v___x_376_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_371_, v___x_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_quoteNameMk(v___x_375_);
v___y_350_ = v___x_367_;
v___y_351_ = v___x_374_;
v___y_352_ = v___x_373_;
v___y_353_ = v___x_366_;
v___y_354_ = v___x_377_;
goto v___jp_349_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v___x_375_);
v_val_378_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_val_378_);
lean_dec_ref_known(v___x_376_, 1);
v___x_379_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_380_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_381_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_382_ = lean_string_intercalate(v___x_381_, v_val_378_);
v___x_383_ = lean_string_append(v___x_380_, v___x_382_);
lean_dec_ref(v___x_382_);
v___x_384_ = lean_box(2);
v___x_385_ = l_Lean_Syntax_mkNameLit(v___x_383_, v___x_384_);
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
v___x_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_384_);
lean_ctor_set(v___x_388_, 1, v___x_379_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
v___y_350_ = v___x_367_;
v___y_351_ = v___x_374_;
v___y_352_ = v___x_373_;
v___y_353_ = v___x_366_;
v___y_354_ = v___x_388_;
goto v___jp_349_;
}
}
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_unsigned_to_nat(2u);
v___x_424_ = l_Lean_Syntax_getArg(v_x_156_, v___x_423_);
v___x_425_ = l_Lean_Syntax_matchesNull(v___x_424_, v___x_422_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec(v_x_156_);
v___x_426_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v_id_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v_id_428_ = l_Lean_Syntax_getArg(v_x_156_, v___x_427_);
v___x_429_ = lean_unsigned_to_nat(3u);
v___x_430_ = l_Lean_Syntax_getArg(v_x_156_, v___x_429_);
lean_dec(v_x_156_);
if (v___x_162_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc(v___x_430_);
v___x_472_ = l_Lean_Syntax_isOfKind(v___x_430_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v_quotContext_473_; lean_object* v_currMacroScope_474_; lean_object* v_ref_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___y_486_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_quotContext_473_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_474_ = lean_ctor_get(v_a_157_, 2);
v_ref_475_ = lean_ctor_get(v_a_157_, 5);
v___x_476_ = l_Lean_SourceInfo_fromRef(v_ref_475_, v___x_162_);
v___x_477_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_478_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
v___x_479_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48));
lean_inc(v_currMacroScope_474_);
lean_inc(v_quotContext_473_);
v___x_480_ = l_Lean_addMacroScope(v_quotContext_473_, v___x_479_, v_currMacroScope_474_);
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50));
lean_inc(v___x_476_);
v___x_483_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_483_, 0, v___x_476_);
lean_ctor_set(v___x_483_, 1, v___x_478_);
lean_ctor_set(v___x_483_, 2, v___x_480_);
lean_ctor_set(v___x_483_, 3, v___x_482_);
v___x_484_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_490_ = l_Lean_TSyntax_getId(v_id_428_);
lean_dec(v_id_428_);
lean_inc(v___x_490_);
v___x_491_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_481_, v___x_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_quoteNameMk(v___x_490_);
v___y_486_ = v___x_492_;
goto v___jp_485_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___x_490_);
v_val_493_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v___x_491_, 1);
v___x_494_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_495_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_496_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_497_ = lean_string_intercalate(v___x_496_, v_val_493_);
v___x_498_ = lean_string_append(v___x_495_, v___x_497_);
lean_dec_ref(v___x_497_);
v___x_499_ = lean_box(2);
v___x_500_ = l_Lean_Syntax_mkNameLit(v___x_498_, v___x_499_);
v___x_501_ = lean_mk_empty_array_with_capacity(v___x_427_);
v___x_502_ = lean_array_push(v___x_501_, v___x_500_);
v___x_503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_503_, 0, v___x_499_);
lean_ctor_set(v___x_503_, 1, v___x_494_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
v___y_486_ = v___x_503_;
goto v___jp_485_;
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_inc(v___x_476_);
v___x_487_ = l_Lean_Syntax_node2(v___x_476_, v___x_484_, v___y_486_, v___x_430_);
v___x_488_ = l_Lean_Syntax_node2(v___x_476_, v___x_477_, v___x_483_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_158_);
return v___x_489_;
}
}
else
{
goto v___jp_444_;
}
}
else
{
goto v___jp_444_;
}
v___jp_431_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_437_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
v___x_438_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16));
lean_inc_n(v___y_435_, 3);
v___x_439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_439_, 0, v___y_435_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_Syntax_node2(v___y_435_, v___x_437_, v___x_439_, v___x_430_);
lean_inc(v___y_433_);
v___x_441_ = l_Lean_Syntax_node2(v___y_435_, v___y_433_, v___y_436_, v___x_440_);
lean_inc(v___y_432_);
v___x_442_ = l_Lean_Syntax_node2(v___y_435_, v___y_432_, v___y_434_, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v_a_158_);
return v___x_443_;
}
v___jp_444_:
{
lean_object* v_quotContext_445_; lean_object* v_currMacroScope_446_; lean_object* v_ref_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_quotContext_445_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_446_ = lean_ctor_get(v_a_157_, 2);
v_ref_447_ = lean_ctor_get(v_a_157_, 5);
v___x_448_ = l_Lean_SourceInfo_fromRef(v_ref_447_, v___x_162_);
v___x_449_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_450_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
v___x_451_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48));
lean_inc(v_currMacroScope_446_);
lean_inc(v_quotContext_445_);
v___x_452_ = l_Lean_addMacroScope(v_quotContext_445_, v___x_451_, v_currMacroScope_446_);
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50));
lean_inc(v___x_448_);
v___x_455_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_455_, 0, v___x_448_);
lean_ctor_set(v___x_455_, 1, v___x_450_);
lean_ctor_set(v___x_455_, 2, v___x_452_);
lean_ctor_set(v___x_455_, 3, v___x_454_);
v___x_456_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_457_ = l_Lean_TSyntax_getId(v_id_428_);
lean_dec(v_id_428_);
lean_inc(v___x_457_);
v___x_458_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_453_, v___x_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_quoteNameMk(v___x_457_);
v___y_432_ = v___x_449_;
v___y_433_ = v___x_456_;
v___y_434_ = v___x_455_;
v___y_435_ = v___x_448_;
v___y_436_ = v___x_459_;
goto v___jp_431_;
}
else
{
lean_object* v_val_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v___x_457_);
v_val_460_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v___x_458_, 1);
v___x_461_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_462_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_463_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_464_ = lean_string_intercalate(v___x_463_, v_val_460_);
v___x_465_ = lean_string_append(v___x_462_, v___x_464_);
lean_dec_ref(v___x_464_);
v___x_466_ = lean_box(2);
v___x_467_ = l_Lean_Syntax_mkNameLit(v___x_465_, v___x_466_);
v___x_468_ = lean_mk_empty_array_with_capacity(v___x_427_);
v___x_469_ = lean_array_push(v___x_468_, v___x_467_);
v___x_470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_470_, 0, v___x_466_);
lean_ctor_set(v___x_470_, 1, v___x_461_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
v___y_432_ = v___x_449_;
v___y_433_ = v___x_456_;
v___y_434_ = v___x_455_;
v___y_435_ = v___x_448_;
v___y_436_ = v___x_470_;
goto v___jp_431_;
}
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = l_Lean_Syntax_getArg(v_x_156_, v___x_505_);
v___x_507_ = l_Lean_Syntax_matchesNull(v___x_506_, v___x_504_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_x_156_);
v___x_508_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_id_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = l_Lean_Syntax_getArg(v_x_156_, v___x_509_);
v___x_511_ = lean_unsigned_to_nat(2u);
v_id_512_ = l_Lean_Syntax_getArg(v_x_156_, v___x_511_);
v___x_513_ = lean_unsigned_to_nat(4u);
v___x_514_ = l_Lean_Syntax_getArg(v_x_156_, v___x_513_);
lean_dec(v_x_156_);
if (v___x_160_ == 0)
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc(v___x_514_);
v___x_556_ = l_Lean_Syntax_isOfKind(v___x_514_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v_quotContext_557_; lean_object* v_currMacroScope_558_; lean_object* v_ref_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___y_570_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_quotContext_557_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_558_ = lean_ctor_get(v_a_157_, 2);
v_ref_559_ = lean_ctor_get(v_a_157_, 5);
v___x_560_ = l_Lean_SourceInfo_fromRef(v_ref_559_, v___x_160_);
v___x_561_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_562_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
v___x_563_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54));
lean_inc(v_currMacroScope_558_);
lean_inc(v_quotContext_557_);
v___x_564_ = l_Lean_addMacroScope(v_quotContext_557_, v___x_563_, v_currMacroScope_558_);
v___x_565_ = lean_box(0);
v___x_566_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56));
lean_inc(v___x_560_);
v___x_567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_567_, 0, v___x_560_);
lean_ctor_set(v___x_567_, 1, v___x_562_);
lean_ctor_set(v___x_567_, 2, v___x_564_);
lean_ctor_set(v___x_567_, 3, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_574_ = l_Lean_TSyntax_getId(v_id_512_);
lean_dec(v_id_512_);
lean_inc(v___x_574_);
v___x_575_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_565_, v___x_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_quoteNameMk(v___x_574_);
v___y_570_ = v___x_576_;
goto v___jp_569_;
}
else
{
lean_object* v_val_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_574_);
v_val_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_575_, 1);
v___x_578_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_579_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_580_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_581_ = lean_string_intercalate(v___x_580_, v_val_577_);
v___x_582_ = lean_string_append(v___x_579_, v___x_581_);
lean_dec_ref(v___x_581_);
v___x_583_ = lean_box(2);
v___x_584_ = l_Lean_Syntax_mkNameLit(v___x_582_, v___x_583_);
v___x_585_ = lean_mk_empty_array_with_capacity(v___x_509_);
v___x_586_ = lean_array_push(v___x_585_, v___x_584_);
v___x_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_587_, 0, v___x_583_);
lean_ctor_set(v___x_587_, 1, v___x_578_);
lean_ctor_set(v___x_587_, 2, v___x_586_);
v___y_570_ = v___x_587_;
goto v___jp_569_;
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_inc(v___x_560_);
v___x_571_ = l_Lean_Syntax_node3(v___x_560_, v___x_568_, v___x_510_, v___y_570_, v___x_514_);
v___x_572_ = l_Lean_Syntax_node2(v___x_560_, v___x_561_, v___x_567_, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_a_158_);
return v___x_573_;
}
}
else
{
goto v___jp_528_;
}
}
else
{
goto v___jp_528_;
}
v___jp_515_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_521_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
v___x_522_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16));
lean_inc_n(v___y_517_, 3);
v___x_523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_523_, 0, v___y_517_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_Syntax_node2(v___y_517_, v___x_521_, v___x_523_, v___x_514_);
lean_inc(v___y_519_);
v___x_525_ = l_Lean_Syntax_node3(v___y_517_, v___y_519_, v___x_510_, v___y_520_, v___x_524_);
lean_inc(v___y_518_);
v___x_526_ = l_Lean_Syntax_node2(v___y_517_, v___y_518_, v___y_516_, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_a_158_);
return v___x_527_;
}
v___jp_528_:
{
lean_object* v_quotContext_529_; lean_object* v_currMacroScope_530_; lean_object* v_ref_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_quotContext_529_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_530_ = lean_ctor_get(v_a_157_, 2);
v_ref_531_ = lean_ctor_get(v_a_157_, 5);
v___x_532_ = l_Lean_SourceInfo_fromRef(v_ref_531_, v___x_160_);
v___x_533_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_534_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
v___x_535_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54));
lean_inc(v_currMacroScope_530_);
lean_inc(v_quotContext_529_);
v___x_536_ = l_Lean_addMacroScope(v_quotContext_529_, v___x_535_, v_currMacroScope_530_);
v___x_537_ = lean_box(0);
v___x_538_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56));
lean_inc(v___x_532_);
v___x_539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_539_, 0, v___x_532_);
lean_ctor_set(v___x_539_, 1, v___x_534_);
lean_ctor_set(v___x_539_, 2, v___x_536_);
lean_ctor_set(v___x_539_, 3, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_541_ = l_Lean_TSyntax_getId(v_id_512_);
lean_dec(v_id_512_);
lean_inc(v___x_541_);
v___x_542_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_537_, v___x_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_quoteNameMk(v___x_541_);
v___y_516_ = v___x_539_;
v___y_517_ = v___x_532_;
v___y_518_ = v___x_533_;
v___y_519_ = v___x_540_;
v___y_520_ = v___x_543_;
goto v___jp_515_;
}
else
{
lean_object* v_val_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v___x_541_);
v_val_544_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v___x_542_, 1);
v___x_545_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_546_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_547_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_548_ = lean_string_intercalate(v___x_547_, v_val_544_);
v___x_549_ = lean_string_append(v___x_546_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = lean_box(2);
v___x_551_ = l_Lean_Syntax_mkNameLit(v___x_549_, v___x_550_);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_509_);
v___x_553_ = lean_array_push(v___x_552_, v___x_551_);
v___x_554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_550_);
lean_ctor_set(v___x_554_, 1, v___x_545_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
v___y_516_ = v___x_539_;
v___y_517_ = v___x_532_;
v___y_518_ = v___x_533_;
v___y_519_ = v___x_540_;
v___y_520_ = v___x_554_;
goto v___jp_515_;
}
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_id_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_unsigned_to_nat(1u);
v_id_590_ = l_Lean_Syntax_getArg(v_x_156_, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
lean_inc(v_id_590_);
v___x_592_ = l_Lean_Syntax_isOfKind(v_id_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = l_Lean_Syntax_getArg(v_x_156_, v___x_593_);
v___x_595_ = l_Lean_Syntax_matchesNull(v___x_594_, v___x_588_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v_id_590_);
lean_dec(v_x_156_);
v___x_596_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_596_;
}
else
{
lean_object* v_quotContext_597_; lean_object* v_currMacroScope_598_; lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___y_612_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_quotContext_597_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_598_ = lean_ctor_get(v_a_157_, 2);
v_ref_599_ = lean_ctor_get(v_a_157_, 5);
v___x_600_ = lean_unsigned_to_nat(3u);
v___x_601_ = l_Lean_Syntax_getArg(v_x_156_, v___x_600_);
lean_dec(v_x_156_);
v___x_602_ = l_Lean_SourceInfo_fromRef(v_ref_599_, v___x_592_);
v___x_603_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_604_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
v___x_605_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62));
lean_inc(v_currMacroScope_598_);
lean_inc(v_quotContext_597_);
v___x_606_ = l_Lean_addMacroScope(v_quotContext_597_, v___x_605_, v_currMacroScope_598_);
v___x_607_ = lean_box(0);
v___x_608_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64));
lean_inc(v___x_602_);
v___x_609_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_609_, 0, v___x_602_);
lean_ctor_set(v___x_609_, 1, v___x_604_);
lean_ctor_set(v___x_609_, 2, v___x_606_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_616_ = l_Lean_TSyntax_getId(v_id_590_);
lean_dec(v_id_590_);
lean_inc(v___x_616_);
v___x_617_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_607_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_quoteNameMk(v___x_616_);
v___y_612_ = v___x_618_;
goto v___jp_611_;
}
else
{
lean_object* v_val_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___x_616_);
v_val_619_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_617_, 1);
v___x_620_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_621_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_622_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_623_ = lean_string_intercalate(v___x_622_, v_val_619_);
v___x_624_ = lean_string_append(v___x_621_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_box(2);
v___x_626_ = l_Lean_Syntax_mkNameLit(v___x_624_, v___x_625_);
v___x_627_ = lean_mk_empty_array_with_capacity(v___x_589_);
v___x_628_ = lean_array_push(v___x_627_, v___x_626_);
v___x_629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_629_, 0, v___x_625_);
lean_ctor_set(v___x_629_, 1, v___x_620_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
v___y_612_ = v___x_629_;
goto v___jp_611_;
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc(v___x_602_);
v___x_613_ = l_Lean_Syntax_node2(v___x_602_, v___x_610_, v___y_612_, v___x_601_);
v___x_614_ = l_Lean_Syntax_node2(v___x_602_, v___x_603_, v___x_609_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_a_158_);
return v___x_615_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(2u);
v___x_631_ = l_Lean_Syntax_getArg(v_x_156_, v___x_630_);
v___x_632_ = l_Lean_Syntax_matchesNull(v___x_631_, v___x_588_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v_id_590_);
lean_dec(v_x_156_);
v___x_633_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(3u);
v___x_635_ = l_Lean_Syntax_getArg(v_x_156_, v___x_634_);
lean_dec(v_x_156_);
v___x_636_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc(v___x_635_);
v___x_637_ = l_Lean_Syntax_isOfKind(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v_quotContext_638_; lean_object* v_currMacroScope_639_; lean_object* v_ref_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___y_651_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_quotContext_638_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_639_ = lean_ctor_get(v_a_157_, 2);
v_ref_640_ = lean_ctor_get(v_a_157_, 5);
v___x_641_ = l_Lean_SourceInfo_fromRef(v_ref_640_, v___x_637_);
v___x_642_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_643_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
v___x_644_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62));
lean_inc(v_currMacroScope_639_);
lean_inc(v_quotContext_638_);
v___x_645_ = l_Lean_addMacroScope(v_quotContext_638_, v___x_644_, v_currMacroScope_639_);
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64));
lean_inc(v___x_641_);
v___x_648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_648_, 0, v___x_641_);
lean_ctor_set(v___x_648_, 1, v___x_643_);
lean_ctor_set(v___x_648_, 2, v___x_645_);
lean_ctor_set(v___x_648_, 3, v___x_647_);
v___x_649_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_655_ = l_Lean_TSyntax_getId(v_id_590_);
lean_dec(v_id_590_);
lean_inc(v___x_655_);
v___x_656_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_646_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_quoteNameMk(v___x_655_);
v___y_651_ = v___x_657_;
goto v___jp_650_;
}
else
{
lean_object* v_val_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v___x_655_);
v_val_658_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v___x_656_, 1);
v___x_659_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_660_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_661_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_662_ = lean_string_intercalate(v___x_661_, v_val_658_);
v___x_663_ = lean_string_append(v___x_660_, v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_box(2);
v___x_665_ = l_Lean_Syntax_mkNameLit(v___x_663_, v___x_664_);
v___x_666_ = lean_mk_empty_array_with_capacity(v___x_589_);
v___x_667_ = lean_array_push(v___x_666_, v___x_665_);
v___x_668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_668_, 0, v___x_664_);
lean_ctor_set(v___x_668_, 1, v___x_659_);
lean_ctor_set(v___x_668_, 2, v___x_667_);
v___y_651_ = v___x_668_;
goto v___jp_650_;
}
v___jp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc(v___x_641_);
v___x_652_ = l_Lean_Syntax_node2(v___x_641_, v___x_649_, v___y_651_, v___x_635_);
v___x_653_ = l_Lean_Syntax_node2(v___x_641_, v___x_642_, v___x_648_, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_a_158_);
return v___x_654_;
}
}
else
{
lean_object* v_quotContext_669_; lean_object* v_currMacroScope_670_; lean_object* v_ref_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___y_683_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_quotContext_669_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_670_ = lean_ctor_get(v_a_157_, 2);
v_ref_671_ = lean_ctor_get(v_a_157_, 5);
v___x_672_ = 0;
v___x_673_ = l_Lean_SourceInfo_fromRef(v_ref_671_, v___x_672_);
v___x_674_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_675_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
v___x_676_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62));
lean_inc(v_currMacroScope_670_);
lean_inc(v_quotContext_669_);
v___x_677_ = l_Lean_addMacroScope(v_quotContext_669_, v___x_676_, v_currMacroScope_670_);
v___x_678_ = lean_box(0);
v___x_679_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64));
lean_inc(v___x_673_);
v___x_680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_680_, 0, v___x_673_);
lean_ctor_set(v___x_680_, 1, v___x_675_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
lean_ctor_set(v___x_680_, 3, v___x_679_);
v___x_681_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26));
v___x_691_ = l_Lean_TSyntax_getId(v_id_590_);
lean_dec(v_id_590_);
lean_inc(v___x_691_);
v___x_692_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_678_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_quoteNameMk(v___x_691_);
v___y_683_ = v___x_693_;
goto v___jp_682_;
}
else
{
lean_object* v_val_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v___x_691_);
v_val_694_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_692_, 1);
v___x_695_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_696_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_697_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30));
v___x_698_ = lean_string_intercalate(v___x_697_, v_val_694_);
v___x_699_ = lean_string_append(v___x_696_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_box(2);
v___x_701_ = l_Lean_Syntax_mkNameLit(v___x_699_, v___x_700_);
v___x_702_ = lean_mk_empty_array_with_capacity(v___x_589_);
v___x_703_ = lean_array_push(v___x_702_, v___x_701_);
v___x_704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_704_, 0, v___x_700_);
lean_ctor_set(v___x_704_, 1, v___x_695_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
v___y_683_ = v___x_704_;
goto v___jp_682_;
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_684_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
v___x_685_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16));
lean_inc_n(v___x_673_, 3);
v___x_686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_673_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_Syntax_node2(v___x_673_, v___x_684_, v___x_686_, v___x_635_);
v___x_688_ = l_Lean_Syntax_node2(v___x_673_, v___x_681_, v___y_683_, v___x_687_);
v___x_689_ = l_Lean_Syntax_node2(v___x_673_, v___x_674_, v___x_680_, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_a_158_);
return v___x_690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(v_x_705_, v_a_706_, v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_dec(v_b_710_);
lean_dec(v_a_709_);
return v_x_711_;
}
else
{
lean_object* v_key_712_; lean_object* v_value_713_; lean_object* v_tail_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_726_; 
v_key_712_ = lean_ctor_get(v_x_711_, 0);
v_value_713_ = lean_ctor_get(v_x_711_, 1);
v_tail_714_ = lean_ctor_get(v_x_711_, 2);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_726_ == 0)
{
v___x_716_ = v_x_711_;
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_tail_714_);
lean_inc(v_value_713_);
lean_inc(v_key_712_);
lean_dec(v_x_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
uint8_t v___x_718_; 
v___x_718_ = lean_name_eq(v_key_712_, v_a_709_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_709_, v_b_710_, v_tail_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_719_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_key_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_value_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
else
{
lean_object* v___x_724_; 
lean_dec(v_value_713_);
lean_dec(v_key_712_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_b_710_);
lean_ctor_set(v___x_716_, 0, v_a_709_);
v___x_724_ = v___x_716_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_709_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_b_710_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_tail_714_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
return v_x_727_;
}
else
{
lean_object* v_key_729_; lean_object* v_value_730_; lean_object* v_tail_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_757_; 
v_key_729_ = lean_ctor_get(v_x_728_, 0);
v_value_730_ = lean_ctor_get(v_x_728_, 1);
v_tail_731_ = lean_ctor_get(v_x_728_, 2);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_757_ == 0)
{
v___x_733_ = v_x_728_;
v_isShared_734_ = v_isSharedCheck_757_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_tail_731_);
lean_inc(v_value_730_);
lean_inc(v_key_729_);
lean_dec(v_x_728_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_757_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; uint64_t v___y_737_; 
v___x_735_ = lean_array_get_size(v_x_727_);
if (lean_obj_tag(v_key_729_) == 0)
{
uint64_t v___x_755_; 
v___x_755_ = 1723ULL;
v___y_737_ = v___x_755_;
goto v___jp_736_;
}
else
{
uint64_t v_hash_756_; 
v_hash_756_ = lean_ctor_get_uint64(v_key_729_, sizeof(void*)*2);
v___y_737_ = v_hash_756_;
goto v___jp_736_;
}
v___jp_736_:
{
uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v_fold_740_; uint64_t v___x_741_; uint64_t v___x_742_; uint64_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_738_ = 32ULL;
v___x_739_ = lean_uint64_shift_right(v___y_737_, v___x_738_);
v_fold_740_ = lean_uint64_xor(v___y_737_, v___x_739_);
v___x_741_ = 16ULL;
v___x_742_ = lean_uint64_shift_right(v_fold_740_, v___x_741_);
v___x_743_ = lean_uint64_xor(v_fold_740_, v___x_742_);
v___x_744_ = lean_uint64_to_usize(v___x_743_);
v___x_745_ = lean_usize_of_nat(v___x_735_);
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_sub(v___x_745_, v___x_746_);
v___x_748_ = lean_usize_land(v___x_744_, v___x_747_);
v___x_749_ = lean_array_uget_borrowed(v_x_727_, v___x_748_);
lean_inc(v___x_749_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 2, v___x_749_);
v___x_751_ = v___x_733_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_key_729_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_value_730_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v___x_749_);
v___x_751_ = v_reuseFailAlloc_754_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
v___x_752_ = lean_array_uset(v_x_727_, v___x_748_, v___x_751_);
v_x_727_ = v___x_752_;
v_x_728_ = v_tail_731_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_758_, lean_object* v_source_759_, lean_object* v_target_760_){
_start:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_array_get_size(v_source_759_);
v___x_762_ = lean_nat_dec_lt(v_i_758_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec_ref(v_source_759_);
lean_dec(v_i_758_);
return v_target_760_;
}
else
{
lean_object* v_es_763_; lean_object* v___x_764_; lean_object* v_source_765_; lean_object* v_target_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_es_763_ = lean_array_fget(v_source_759_, v_i_758_);
v___x_764_ = lean_box(0);
v_source_765_ = lean_array_fset(v_source_759_, v_i_758_, v___x_764_);
v_target_766_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_760_, v_es_763_);
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_i_758_, v___x_767_);
lean_dec(v_i_758_);
v_i_758_ = v___x_768_;
v_source_759_ = v_source_765_;
v_target_760_ = v_target_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(lean_object* v_data_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_nbuckets_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_771_ = lean_array_get_size(v_data_770_);
v___x_772_ = lean_unsigned_to_nat(2u);
v_nbuckets_773_ = lean_nat_mul(v___x_771_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_box(0);
v___x_776_ = lean_mk_array(v_nbuckets_773_, v___x_775_);
v___x_777_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_774_, v_data_770_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_778_, lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
uint8_t v___x_780_; 
v___x_780_ = 0;
return v___x_780_;
}
else
{
lean_object* v_key_781_; lean_object* v_tail_782_; uint8_t v___x_783_; 
v_key_781_ = lean_ctor_get(v_x_779_, 0);
v_tail_782_ = lean_ctor_get(v_x_779_, 2);
v___x_783_ = lean_name_eq(v_key_781_, v_a_778_);
if (v___x_783_ == 0)
{
v_x_779_ = v_tail_782_;
goto _start;
}
else
{
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec(v_a_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object* v_m_789_, lean_object* v_a_790_, lean_object* v_b_791_){
_start:
{
lean_object* v_size_792_; lean_object* v_buckets_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_839_; 
v_size_792_ = lean_ctor_get(v_m_789_, 0);
v_buckets_793_ = lean_ctor_get(v_m_789_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_m_789_);
if (v_isSharedCheck_839_ == 0)
{
v___x_795_ = v_m_789_;
v_isShared_796_ = v_isSharedCheck_839_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_buckets_793_);
lean_inc(v_size_792_);
lean_dec(v_m_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_839_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; uint64_t v___y_799_; 
v___x_797_ = lean_array_get_size(v_buckets_793_);
if (lean_obj_tag(v_a_790_) == 0)
{
uint64_t v___x_837_; 
v___x_837_ = 1723ULL;
v___y_799_ = v___x_837_;
goto v___jp_798_;
}
else
{
uint64_t v_hash_838_; 
v_hash_838_ = lean_ctor_get_uint64(v_a_790_, sizeof(void*)*2);
v___y_799_ = v_hash_838_;
goto v___jp_798_;
}
v___jp_798_:
{
uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v_fold_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; size_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v_bkt_811_; uint8_t v___x_812_; 
v___x_800_ = 32ULL;
v___x_801_ = lean_uint64_shift_right(v___y_799_, v___x_800_);
v_fold_802_ = lean_uint64_xor(v___y_799_, v___x_801_);
v___x_803_ = 16ULL;
v___x_804_ = lean_uint64_shift_right(v_fold_802_, v___x_803_);
v___x_805_ = lean_uint64_xor(v_fold_802_, v___x_804_);
v___x_806_ = lean_uint64_to_usize(v___x_805_);
v___x_807_ = lean_usize_of_nat(v___x_797_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_sub(v___x_807_, v___x_808_);
v___x_810_ = lean_usize_land(v___x_806_, v___x_809_);
v_bkt_811_ = lean_array_uget_borrowed(v_buckets_793_, v___x_810_);
v___x_812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_790_, v_bkt_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v_size_x27_814_; lean_object* v___x_815_; lean_object* v_buckets_x27_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_813_ = lean_unsigned_to_nat(1u);
v_size_x27_814_ = lean_nat_add(v_size_792_, v___x_813_);
lean_dec(v_size_792_);
lean_inc(v_bkt_811_);
v___x_815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_815_, 0, v_a_790_);
lean_ctor_set(v___x_815_, 1, v_b_791_);
lean_ctor_set(v___x_815_, 2, v_bkt_811_);
v_buckets_x27_816_ = lean_array_uset(v_buckets_793_, v___x_810_, v___x_815_);
v___x_817_ = lean_unsigned_to_nat(4u);
v___x_818_ = lean_nat_mul(v_size_x27_814_, v___x_817_);
v___x_819_ = lean_unsigned_to_nat(3u);
v___x_820_ = lean_nat_div(v___x_818_, v___x_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_array_get_size(v_buckets_x27_816_);
v___x_822_ = lean_nat_dec_le(v___x_820_, v___x_821_);
lean_dec(v___x_820_);
if (v___x_822_ == 0)
{
lean_object* v_val_823_; lean_object* v___x_825_; 
v_val_823_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_816_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_val_823_);
lean_ctor_set(v___x_795_, 0, v_size_x27_814_);
v___x_825_ = v___x_795_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_size_x27_814_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_val_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_828_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_buckets_x27_816_);
lean_ctor_set(v___x_795_, 0, v_size_x27_814_);
v___x_828_ = v___x_795_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_size_x27_814_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_buckets_x27_816_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v___x_830_; lean_object* v_buckets_x27_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
lean_inc(v_bkt_811_);
v___x_830_ = lean_box(0);
v_buckets_x27_831_ = lean_array_uset(v_buckets_793_, v___x_810_, v___x_830_);
v___x_832_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_790_, v_b_791_, v_bkt_811_);
v___x_833_ = lean_array_uset(v_buckets_x27_831_, v___x_810_, v___x_832_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_833_);
v___x_835_ = v___x_795_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_size_792_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object* v_as_x27_840_, lean_object* v_b_841_){
_start:
{
if (lean_obj_tag(v_as_x27_840_) == 0)
{
return v_b_841_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v_r_846_; 
v_head_842_ = lean_ctor_get(v_as_x27_840_, 0);
v_tail_843_ = lean_ctor_get(v_as_x27_840_, 1);
v_fst_844_ = lean_ctor_get(v_head_842_, 0);
v_snd_845_ = lean_ctor_get(v_head_842_, 1);
lean_inc(v_snd_845_);
lean_inc(v_fst_844_);
v_r_846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_841_, v_fst_844_, v_snd_845_);
v_as_x27_840_ = v_tail_843_;
v_b_841_ = v_r_846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_848_, lean_object* v_b_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_848_, v_b_849_);
lean_dec(v_as_x27_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* v_m_851_, lean_object* v_l_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_852_, v_m_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object* v_m_854_, lean_object* v_l_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(v_m_854_, v_l_855_);
lean_dec(v_l_855_);
return v_res_856_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_box(0);
v___x_920_ = lean_unsigned_to_nat(16u);
v___x_921_ = lean_mk_array(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
v___x_926_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21));
v___x_927_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap(void){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_929_, lean_object* v_m_930_, lean_object* v_a_931_, lean_object* v_b_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_930_, v_a_931_, v_b_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object* v_as_934_, lean_object* v_as_x27_935_, lean_object* v_b_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_935_, v_b_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object* v_as_939_, lean_object* v_as_x27_940_, lean_object* v_b_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_939_, v_as_x27_940_, v_b_941_, v_a_942_);
lean_dec(v_as_x27_940_);
lean_dec(v_as_939_);
return v_res_943_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_944_, lean_object* v_a_945_, lean_object* v_x_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_948_, lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_948_, v_a_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec(v_a_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_953_, lean_object* v_data_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_956_, lean_object* v_a_957_, lean_object* v_b_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_957_, v_b_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_961_, lean_object* v_i_962_, lean_object* v_source_963_, lean_object* v_target_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_962_, v_source_963_, v_target_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_967_, v_x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object* v_name_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_env_974_; lean_object* v___x_975_; lean_object* v_toEnvExtension_976_; lean_object* v_asyncMode_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_973_ = lean_st_ref_get(v___y_971_);
v_env_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc_ref(v_env_974_);
lean_dec(v___x_973_);
v___x_975_ = l_Lean_errorExplanationExt;
v_toEnvExtension_976_ = lean_ctor_get(v___x_975_, 0);
v_asyncMode_977_ = lean_ctor_get(v_toEnvExtension_976_, 2);
v___x_978_ = lean_box(1);
v___x_979_ = lean_box(0);
v___x_980_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_978_, v___x_975_, v_env_974_, v_asyncMode_977_, v___x_979_);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_980_, v_name_970_);
lean_dec(v___x_980_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object* v_name_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec(v_name_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object* v_name_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_987_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object* v_name_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v_name_996_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(lean_object* v_msgData_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v___x_1013_; lean_object* v_mctx_1014_; lean_object* v_lctx_1015_; lean_object* v_options_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1011_ = lean_st_ref_get(v___y_1009_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1013_ = lean_st_ref_get(v___y_1007_);
v_mctx_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_mctx_1014_);
lean_dec(v___x_1013_);
v_lctx_1015_ = lean_ctor_get(v___y_1006_, 2);
v_options_1016_ = lean_ctor_get(v___y_1008_, 1);
lean_inc_ref(v_options_1016_);
lean_inc_ref(v_lctx_1015_);
v___x_1017_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1017_, 0, v_env_1012_);
lean_ctor_set(v___x_1017_, 1, v_mctx_1014_);
lean_ctor_set(v___x_1017_, 2, v_lctx_1015_);
lean_ctor_set(v___x_1017_, 3, v_options_1016_);
v___x_1018_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v_msgData_1005_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(lean_object* v_msgData_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1026_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1027_; double v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_float_of_nat(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object* v_cls_1032_, lean_object* v_msg_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_ref_1039_; lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1085_; 
v_ref_1039_ = lean_ctor_get(v___y_1036_, 4);
v___x_1040_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1085_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1085_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v_traceState_1046_; lean_object* v_env_1047_; lean_object* v_nextMacroScope_1048_; lean_object* v_ngen_1049_; lean_object* v_auxDeclNGen_1050_; lean_object* v_cache_1051_; lean_object* v_messages_1052_; lean_object* v_infoState_1053_; lean_object* v_snapshotTasks_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1084_; 
v___x_1045_ = lean_st_ref_take(v___y_1037_);
v_traceState_1046_ = lean_ctor_get(v___x_1045_, 4);
v_env_1047_ = lean_ctor_get(v___x_1045_, 0);
v_nextMacroScope_1048_ = lean_ctor_get(v___x_1045_, 1);
v_ngen_1049_ = lean_ctor_get(v___x_1045_, 2);
v_auxDeclNGen_1050_ = lean_ctor_get(v___x_1045_, 3);
v_cache_1051_ = lean_ctor_get(v___x_1045_, 5);
v_messages_1052_ = lean_ctor_get(v___x_1045_, 6);
v_infoState_1053_ = lean_ctor_get(v___x_1045_, 7);
v_snapshotTasks_1054_ = lean_ctor_get(v___x_1045_, 8);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1056_ = v___x_1045_;
v_isShared_1057_ = v_isSharedCheck_1084_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snapshotTasks_1054_);
lean_inc(v_infoState_1053_);
lean_inc(v_messages_1052_);
lean_inc(v_cache_1051_);
lean_inc(v_traceState_1046_);
lean_inc(v_auxDeclNGen_1050_);
lean_inc(v_ngen_1049_);
lean_inc(v_nextMacroScope_1048_);
lean_inc(v_env_1047_);
lean_dec(v___x_1045_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1084_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
uint64_t v_tid_1058_; lean_object* v_traces_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1083_; 
v_tid_1058_ = lean_ctor_get_uint64(v_traceState_1046_, sizeof(void*)*1);
v_traces_1059_ = lean_ctor_get(v_traceState_1046_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_traceState_1046_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1061_ = v_traceState_1046_;
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_traces_1059_);
lean_dec(v_traceState_1046_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; double v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_1065_ = 0;
v___x_1066_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1067_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1067_, 0, v_cls_1032_);
lean_ctor_set(v___x_1067_, 1, v___x_1063_);
lean_ctor_set(v___x_1067_, 2, v___x_1066_);
lean_ctor_set_float(v___x_1067_, sizeof(void*)*3, v___x_1064_);
lean_ctor_set_float(v___x_1067_, sizeof(void*)*3 + 8, v___x_1064_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*3 + 16, v___x_1065_);
v___x_1068_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_1069_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v_a_1041_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
lean_inc(v_ref_1039_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_ref_1039_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_PersistentArray_push___redArg(v_traces_1059_, v___x_1070_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1071_);
v___x_1073_ = v___x_1061_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1071_);
lean_ctor_set_uint64(v_reuseFailAlloc_1082_, sizeof(void*)*1, v_tid_1058_);
v___x_1073_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___x_1073_);
v___x_1075_ = v___x_1056_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_env_1047_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_nextMacroScope_1048_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_ngen_1049_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_auxDeclNGen_1050_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 5, v_cache_1051_);
lean_ctor_set(v_reuseFailAlloc_1081_, 6, v_messages_1052_);
lean_ctor_set(v_reuseFailAlloc_1081_, 7, v_infoState_1053_);
lean_ctor_set(v_reuseFailAlloc_1081_, 8, v_snapshotTasks_1054_);
v___x_1075_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1076_ = lean_st_ref_put(v___y_1037_, v___x_1075_);
v___x_1077_ = lean_box(0);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1077_);
v___x_1079_ = v___x_1043_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object* v_cls_1086_, lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1086_, v_msg_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object* v_as_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
if (lean_obj_tag(v_as_1097_) == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v_options_1107_; uint8_t v_hasTrace_1108_; 
v_options_1107_ = lean_ctor_get(v___y_1102_, 1);
v_hasTrace_1108_ = lean_ctor_get_uint8(v_options_1107_, sizeof(void*)*1);
if (v_hasTrace_1108_ == 0)
{
lean_object* v_tail_1109_; 
v_tail_1109_ = lean_ctor_get(v_as_1097_, 1);
lean_inc(v_tail_1109_);
lean_dec_ref_known(v_as_1097_, 2);
v_as_1097_ = v_tail_1109_;
goto _start;
}
else
{
lean_object* v_head_1111_; lean_object* v_toCold_1112_; lean_object* v_tail_1113_; lean_object* v_fst_1114_; lean_object* v_snd_1115_; lean_object* v_inheritedTraceOptions_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_head_1111_ = lean_ctor_get(v_as_1097_, 0);
v_toCold_1112_ = lean_ctor_get(v___y_1102_, 0);
lean_inc(v_head_1111_);
v_tail_1113_ = lean_ctor_get(v_as_1097_, 1);
lean_inc(v_tail_1113_);
lean_dec_ref_known(v_as_1097_, 2);
v_fst_1114_ = lean_ctor_get(v_head_1111_, 0);
lean_inc_n(v_fst_1114_, 2);
v_snd_1115_ = lean_ctor_get(v_head_1111_, 1);
lean_inc(v_snd_1115_);
lean_dec(v_head_1111_);
v_inheritedTraceOptions_1116_ = lean_ctor_get(v_toCold_1112_, 4);
v___x_1117_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1118_ = l_Lean_Name_append(v___x_1117_, v_fst_1114_);
v___x_1119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1116_, v_options_1107_, v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v_snd_1115_);
lean_dec(v_fst_1114_);
v_as_1097_ = v_tail_1113_;
goto _start;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_snd_1115_);
v___x_1122_ = l_Lean_MessageData_ofFormat(v___x_1121_);
v___x_1123_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_1114_, v___x_1122_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_dec_ref_known(v___x_1123_, 1);
v_as_1097_ = v_tail_1113_;
goto _start;
}
else
{
lean_dec(v_tail_1113_);
return v___x_1123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object* v_as_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1133_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = l_Lean_maxRecDepthErrorMessage;
v___x_1148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
v___x_1150_ = l_Lean_MessageData_ofFormat(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
v___x_1152_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2));
v___x_1153_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___x_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object* v_ref_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_ref_1154_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object* v_env_1162_, lean_object* v_declName_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_1166_; lean_object* v_env_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1166_ = 0;
v_env_1167_ = l_Lean_Environment_setExporting(v_env_1162_, v___x_1166_);
lean_inc(v_declName_1163_);
v___x_1168_ = l_Lean_mkPrivateName(v_env_1167_, v_declName_1163_);
v___x_1169_ = 1;
lean_inc_ref(v_env_1167_);
v___x_1170_ = l_Lean_Environment_contains(v_env_1167_, v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = l_Lean_privateToUserName(v_declName_1163_);
v___x_1172_ = l_Lean_Environment_contains(v_env_1167_, v___x_1171_, v___x_1169_);
v___x_1173_ = lean_box(v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___y_1165_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v_env_1167_);
lean_dec(v_declName_1163_);
v___x_1175_ = lean_box(v___x_1170_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___y_1165_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object* v_env_1177_, lean_object* v_declName_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_1177_, v_declName_1178_, v___y_1179_, v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object* v_x_1182_, lean_object* v___y_1183_){
_start:
{
if (lean_obj_tag(v_x_1182_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v_x_1182_, 0);
lean_inc(v_a_1184_);
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_a_1184_);
lean_ctor_set(v___x_1185_, 1, v___y_1183_);
return v___x_1185_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v_x_1182_, 0);
lean_inc(v_a_1186_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1186_);
lean_ctor_set(v___x_1187_, 1, v___y_1183_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object* v_x_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_1188_, v___y_1189_);
lean_dec_ref(v_x_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object* v_env_1191_, lean_object* v_stx_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1191_, v_stx_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
if (lean_obj_tag(v_a_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1205_; 
v_a_1197_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v___x_1195_, 0);
lean_dec(v_unused_1206_);
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_box(0);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1197_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1235_; 
v_val_1207_ = lean_ctor_get(v_a_1196_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_a_1196_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1209_ = v_a_1196_;
v_isShared_1210_ = v_isSharedCheck_1235_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_val_1207_);
lean_dec(v_a_1196_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1235_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_snd_1211_; 
v_snd_1211_ = lean_ctor_get(v_val_1207_, 1);
lean_inc(v_snd_1211_);
lean_dec(v_val_1207_);
if (lean_obj_tag(v_snd_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
lean_del_object(v___x_1209_);
v_a_1212_ = lean_ctor_get(v___x_1195_, 1);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1195_, 2);
v_a_1213_ = lean_ctor_get(v_snd_1211_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_snd_1211_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v_snd_1211_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v_snd_1211_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
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
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1218_, v_a_1212_);
lean_dec_ref(v___x_1218_);
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1234_; 
v_a_1222_ = lean_ctor_get(v___x_1195_, 1);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1195_, 2);
v_a_1223_ = lean_ctor_get(v_snd_1211_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_snd_1211_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1225_ = v_snd_1211_;
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v_snd_1211_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_a_1223_);
v___x_1228_ = v___x_1209_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1228_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1230_, v_a_1222_);
lean_dec_ref(v___x_1230_);
return v___x_1231_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1236_ = lean_ctor_get(v___x_1195_, 0);
v_a_1237_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1195_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_inc(v_a_1236_);
lean_dec(v___x_1195_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1236_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object* v_env_1245_, lean_object* v_stx_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_1245_, v_stx_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object* v_env_1250_, lean_object* v_options_1251_, lean_object* v_currNamespace_1252_, lean_object* v_openDecls_1253_, lean_object* v_n_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = l_Lean_ResolveName_resolveGlobalName(v_env_1250_, v_options_1251_, v_currNamespace_1252_, v_openDecls_1253_, v_n_1254_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object* v_env_1259_, lean_object* v_options_1260_, lean_object* v_currNamespace_1261_, lean_object* v_openDecls_1262_, lean_object* v_n_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_1259_, v_options_1260_, v_currNamespace_1261_, v_openDecls_1262_, v_n_1263_, v___y_1264_, v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_options_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object* v_currNamespace_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_currNamespace_1267_);
lean_ctor_set(v___x_1270_, 1, v___y_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_1271_, v___y_1272_, v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object* v_a_1275_, lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_box(0);
return v___x_1277_;
}
else
{
lean_object* v_key_1278_; lean_object* v_value_1279_; lean_object* v_tail_1280_; uint8_t v___x_1281_; 
v_key_1278_ = lean_ctor_get(v_x_1276_, 0);
v_value_1279_ = lean_ctor_get(v_x_1276_, 1);
v_tail_1280_ = lean_ctor_get(v_x_1276_, 2);
v___x_1281_ = lean_name_eq(v_key_1278_, v_a_1275_);
if (v___x_1281_ == 0)
{
v_x_1276_ = v_tail_1280_;
goto _start;
}
else
{
lean_object* v___x_1283_; 
lean_inc(v_value_1279_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_value_1279_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object* v_a_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1284_, v_x_1285_);
lean_dec(v_x_1285_);
lean_dec(v_a_1284_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object* v_m_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_buckets_1289_; lean_object* v___x_1290_; uint64_t v___y_1292_; 
v_buckets_1289_ = lean_ctor_get(v_m_1287_, 1);
v___x_1290_ = lean_array_get_size(v_buckets_1289_);
if (lean_obj_tag(v_a_1288_) == 0)
{
uint64_t v___x_1306_; 
v___x_1306_ = 1723ULL;
v___y_1292_ = v___x_1306_;
goto v___jp_1291_;
}
else
{
uint64_t v_hash_1307_; 
v_hash_1307_ = lean_ctor_get_uint64(v_a_1288_, sizeof(void*)*2);
v___y_1292_ = v_hash_1307_;
goto v___jp_1291_;
}
v___jp_1291_:
{
uint64_t v___x_1293_; uint64_t v___x_1294_; uint64_t v_fold_1295_; uint64_t v___x_1296_; uint64_t v___x_1297_; uint64_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1293_ = 32ULL;
v___x_1294_ = lean_uint64_shift_right(v___y_1292_, v___x_1293_);
v_fold_1295_ = lean_uint64_xor(v___y_1292_, v___x_1294_);
v___x_1296_ = 16ULL;
v___x_1297_ = lean_uint64_shift_right(v_fold_1295_, v___x_1296_);
v___x_1298_ = lean_uint64_xor(v_fold_1295_, v___x_1297_);
v___x_1299_ = lean_uint64_to_usize(v___x_1298_);
v___x_1300_ = lean_usize_of_nat(v___x_1290_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_sub(v___x_1300_, v___x_1301_);
v___x_1303_ = lean_usize_land(v___x_1299_, v___x_1302_);
v___x_1304_ = lean_array_uget_borrowed(v_buckets_1289_, v___x_1303_);
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1288_, v___x_1304_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object* v_m_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_m_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object* v_keys_1311_, lean_object* v_i_1312_, lean_object* v_k_1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_array_get_size(v_keys_1311_);
v___x_1315_ = lean_nat_dec_lt(v_i_1312_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec(v_i_1312_);
return v___x_1315_;
}
else
{
lean_object* v_k_x27_1316_; uint8_t v___x_1317_; 
v_k_x27_1316_ = lean_array_fget_borrowed(v_keys_1311_, v_i_1312_);
v___x_1317_ = l_Lean_instBEqExtraModUse_beq(v_k_1313_, v_k_x27_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_add(v_i_1312_, v___x_1318_);
lean_dec(v_i_1312_);
v_i_1312_ = v___x_1319_;
goto _start;
}
else
{
lean_dec(v_i_1312_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object* v_keys_1321_, lean_object* v_i_1322_, lean_object* v_k_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_1321_, v_i_1322_, v_k_1323_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_keys_1321_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object* v_x_1326_, size_t v_x_1327_, lean_object* v_x_1328_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
lean_object* v_es_1329_; lean_object* v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; lean_object* v_j_1333_; lean_object* v___x_1334_; 
v_es_1329_ = lean_ctor_get(v_x_1326_, 0);
v___x_1330_ = lean_box(2);
v___x_1331_ = ((size_t)31ULL);
v___x_1332_ = lean_usize_land(v_x_1327_, v___x_1331_);
v_j_1333_ = lean_usize_to_nat(v___x_1332_);
v___x_1334_ = lean_array_get_borrowed(v___x_1330_, v_es_1329_, v_j_1333_);
lean_dec(v_j_1333_);
switch(lean_obj_tag(v___x_1334_))
{
case 0:
{
lean_object* v_key_1335_; uint8_t v___x_1336_; 
v_key_1335_ = lean_ctor_get(v___x_1334_, 0);
v___x_1336_ = l_Lean_instBEqExtraModUse_beq(v_x_1328_, v_key_1335_);
return v___x_1336_;
}
case 1:
{
lean_object* v_node_1337_; size_t v___x_1338_; size_t v___x_1339_; 
v_node_1337_ = lean_ctor_get(v___x_1334_, 0);
v___x_1338_ = ((size_t)5ULL);
v___x_1339_ = lean_usize_shift_right(v_x_1327_, v___x_1338_);
v_x_1326_ = v_node_1337_;
v_x_1327_ = v___x_1339_;
goto _start;
}
default: 
{
uint8_t v___x_1341_; 
v___x_1341_ = 0;
return v___x_1341_;
}
}
}
else
{
lean_object* v_ks_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_ks_1342_ = lean_ctor_get(v_x_1326_, 0);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_1342_, v___x_1343_, v_x_1328_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
size_t v_x_20495__boxed_1348_; uint8_t v_res_1349_; lean_object* v_r_1350_; 
v_x_20495__boxed_1348_ = lean_unbox_usize(v_x_1346_);
lean_dec(v_x_1346_);
v_res_1349_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1345_, v_x_20495__boxed_1348_, v_x_1347_);
lean_dec_ref(v_x_1347_);
lean_dec_ref(v_x_1345_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
uint64_t v___x_1353_; size_t v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = l_Lean_instHashableExtraModUse_hash(v_x_1352_);
v___x_1354_ = lean_uint64_to_usize(v___x_1353_);
v___x_1355_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1351_, v___x_1354_, v_x_1352_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_1356_, v_x_1357_);
lean_dec_ref(v_x_1357_);
lean_dec_ref(v_x_1356_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1));
v___x_1363_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0));
v___x_1364_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1363_, v___x_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1365_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1371_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
lean_ctor_set(v___x_1371_, 3, v___x_1370_);
lean_ctor_set(v___x_1371_, 4, v___x_1370_);
lean_ctor_set(v___x_1371_, 5, v___x_1370_);
return v___x_1371_;
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_cls_1383_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_1384_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1385_ = l_Lean_Name_append(v___x_1384_, v_cls_1383_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object* v_mod_1396_, uint8_t v_isMeta_1397_, lean_object* v_hint_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_env_1407_; uint8_t v_isExporting_1408_; lean_object* v___x_1409_; lean_object* v_env_1410_; lean_object* v___x_1411_; lean_object* v_entry_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1406_ = lean_st_ref_get(v___y_1404_);
v_env_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1407_);
lean_dec(v___x_1406_);
v_isExporting_1408_ = lean_ctor_get_uint8(v_env_1407_, sizeof(void*)*8);
lean_dec_ref(v_env_1407_);
v___x_1409_ = lean_st_ref_get(v___y_1404_);
v_env_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_env_1410_);
lean_dec(v___x_1409_);
v___x_1411_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_1396_);
v_entry_1412_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1412_, 0, v_mod_1396_);
lean_ctor_set_uint8(v_entry_1412_, sizeof(void*)*1, v_isExporting_1408_);
lean_ctor_set_uint8(v_entry_1412_, sizeof(void*)*1 + 1, v_isMeta_1397_);
v___x_1413_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1414_ = lean_box(1);
v___x_1415_ = lean_box(0);
v___x_1458_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1411_, v___x_1413_, v_env_1410_, v___x_1414_, v___x_1415_);
v___x_1459_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_1458_, v_entry_1412_);
lean_dec(v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v_options_1460_; uint8_t v_hasTrace_1461_; 
v_options_1460_ = lean_ctor_get(v___y_1403_, 1);
v_hasTrace_1461_ = lean_ctor_get_uint8(v_options_1460_, sizeof(void*)*1);
if (v_hasTrace_1461_ == 0)
{
lean_dec(v_hint_1398_);
lean_dec(v_mod_1396_);
v___y_1417_ = v___y_1402_;
v___y_1418_ = v___y_1404_;
goto v___jp_1416_;
}
else
{
lean_object* v_toCold_1462_; lean_object* v_inheritedTraceOptions_1463_; lean_object* v_cls_1464_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_toCold_1462_ = lean_ctor_get(v___y_1403_, 0);
v_inheritedTraceOptions_1463_ = lean_ctor_get(v_toCold_1462_, 4);
v_cls_1464_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_1484_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
v___x_1485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1463_, v_options_1460_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_dec(v_hint_1398_);
lean_dec(v_mod_1396_);
v___y_1417_ = v___y_1402_;
v___y_1418_ = v___y_1404_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1486_; lean_object* v___y_1488_; 
v___x_1486_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_1408_ == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21));
v___y_1488_ = v___x_1495_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22));
v___y_1488_ = v___x_1496_;
goto v___jp_1487_;
}
v___jp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_inc_ref(v___y_1488_);
v___x_1489_ = l_Lean_stringToMessageData(v___y_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1486_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
if (v_isMeta_1397_ == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_1471_ = v___x_1492_;
v___y_1472_ = v___x_1493_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_1471_ = v___x_1492_;
v___y_1472_ = v___x_1494_;
goto v___jp_1470_;
}
}
}
v___jp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___y_1466_);
lean_ctor_set(v___x_1468_, 1, v___y_1467_);
v___x_1469_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1464_, v___x_1468_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref_known(v___x_1469_, 1);
v___y_1417_ = v___y_1402_;
v___y_1418_ = v___y_1404_;
goto v___jp_1416_;
}
else
{
lean_dec_ref_known(v_entry_1412_, 1);
return v___x_1469_;
}
}
v___jp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
lean_inc_ref(v___y_1472_);
v___x_1473_ = l_Lean_stringToMessageData(v___y_1472_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_MessageData_ofName(v_mod_1396_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_Name_isAnonymous(v_hint_1398_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_1481_ = l_Lean_MessageData_ofName(v_hint_1398_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___y_1466_ = v___x_1478_;
v___y_1467_ = v___x_1482_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1483_; 
lean_dec(v_hint_1398_);
v___x_1483_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
v___y_1466_ = v___x_1478_;
v___y_1467_ = v___x_1483_;
goto v___jp_1465_;
}
}
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref_known(v_entry_1412_, 1);
lean_dec(v_hint_1398_);
lean_dec(v_mod_1396_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
v___jp_1416_:
{
lean_object* v___x_1419_; lean_object* v_toEnvExtension_1420_; lean_object* v_env_1421_; lean_object* v_nextMacroScope_1422_; lean_object* v_ngen_1423_; lean_object* v_auxDeclNGen_1424_; lean_object* v_traceState_1425_; lean_object* v_messages_1426_; lean_object* v_infoState_1427_; lean_object* v_snapshotTasks_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1456_; 
v___x_1419_ = lean_st_ref_take(v___y_1418_);
v_toEnvExtension_1420_ = lean_ctor_get(v___x_1413_, 0);
v_env_1421_ = lean_ctor_get(v___x_1419_, 0);
v_nextMacroScope_1422_ = lean_ctor_get(v___x_1419_, 1);
v_ngen_1423_ = lean_ctor_get(v___x_1419_, 2);
v_auxDeclNGen_1424_ = lean_ctor_get(v___x_1419_, 3);
v_traceState_1425_ = lean_ctor_get(v___x_1419_, 4);
v_messages_1426_ = lean_ctor_get(v___x_1419_, 6);
v_infoState_1427_ = lean_ctor_get(v___x_1419_, 7);
v_snapshotTasks_1428_ = lean_ctor_get(v___x_1419_, 8);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v___x_1419_, 5);
lean_dec(v_unused_1457_);
v___x_1430_ = v___x_1419_;
v_isShared_1431_ = v_isSharedCheck_1456_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snapshotTasks_1428_);
lean_inc(v_infoState_1427_);
lean_inc(v_messages_1426_);
lean_inc(v_traceState_1425_);
lean_inc(v_auxDeclNGen_1424_);
lean_inc(v_ngen_1423_);
lean_inc(v_nextMacroScope_1422_);
lean_inc(v_env_1421_);
lean_dec(v___x_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1456_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_asyncMode_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v_asyncMode_1432_ = lean_ctor_get(v_toEnvExtension_1420_, 2);
v___x_1433_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1413_, v_env_1421_, v_entry_1412_, v_asyncMode_1432_, v___x_1415_);
v___x_1434_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 5, v___x_1434_);
lean_ctor_set(v___x_1430_, 0, v___x_1433_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_nextMacroScope_1422_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_ngen_1423_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_auxDeclNGen_1424_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_traceState_1425_);
lean_ctor_set(v_reuseFailAlloc_1455_, 5, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1455_, 6, v_messages_1426_);
lean_ctor_set(v_reuseFailAlloc_1455_, 7, v_infoState_1427_);
lean_ctor_set(v_reuseFailAlloc_1455_, 8, v_snapshotTasks_1428_);
v___x_1436_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_mctx_1439_; lean_object* v_zetaDeltaFVarIds_1440_; lean_object* v_postponed_1441_; lean_object* v_diag_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1453_; 
v___x_1437_ = lean_st_ref_put(v___y_1418_, v___x_1436_);
v___x_1438_ = lean_st_ref_take(v___y_1417_);
v_mctx_1439_ = lean_ctor_get(v___x_1438_, 0);
v_zetaDeltaFVarIds_1440_ = lean_ctor_get(v___x_1438_, 2);
v_postponed_1441_ = lean_ctor_get(v___x_1438_, 3);
v_diag_1442_ = lean_ctor_get(v___x_1438_, 4);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1438_, 1);
lean_dec(v_unused_1454_);
v___x_1444_ = v___x_1438_;
v_isShared_1445_ = v_isSharedCheck_1453_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_diag_1442_);
lean_inc(v_postponed_1441_);
lean_inc(v_zetaDeltaFVarIds_1440_);
lean_inc(v_mctx_1439_);
lean_dec(v___x_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1453_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_mctx_1439_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_zetaDeltaFVarIds_1440_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_postponed_1441_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_diag_1442_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_st_ref_put(v___y_1417_, v___x_1448_);
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_1499_, lean_object* v_isMeta_1500_, lean_object* v_hint_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_isMeta_boxed_1509_; lean_object* v_res_1510_; 
v_isMeta_boxed_1509_ = lean_unbox(v_isMeta_1500_);
v_res_1510_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_1499_, v_isMeta_boxed_1509_, v_hint_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object* v___x_1511_, lean_object* v_declName_1512_, lean_object* v_as_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1515_, v_sz_1514_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_dec(v_declName_1512_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1516_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v_modules_1527_; lean_object* v___x_1528_; lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v_toImport_1531_; lean_object* v_module_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; 
v___x_1526_ = l_Lean_Environment_header(v___x_1511_);
v_modules_1527_ = lean_ctor_get(v___x_1526_, 3);
lean_inc_ref(v_modules_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1529_ = lean_array_uget_borrowed(v_as_1513_, v_i_1515_);
v___x_1530_ = lean_array_get(v___x_1528_, v_modules_1527_, v_a_1529_);
lean_dec_ref(v_modules_1527_);
v_toImport_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc_ref(v_toImport_1531_);
lean_dec(v___x_1530_);
v_module_1532_ = lean_ctor_get(v_toImport_1531_, 0);
lean_inc(v_module_1532_);
lean_dec_ref(v_toImport_1531_);
v___x_1533_ = 0;
lean_inc(v_declName_1512_);
v___x_1534_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1532_, v___x_1533_, v_declName_1512_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; 
lean_dec_ref_known(v___x_1534_, 1);
v___x_1535_ = lean_box(0);
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_add(v_i_1515_, v___x_1536_);
v_i_1515_ = v___x_1537_;
v_b_1516_ = v___x_1535_;
goto _start;
}
else
{
lean_dec(v_declName_1512_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1539_, lean_object* v_declName_1540_, lean_object* v_as_1541_, lean_object* v_sz_1542_, lean_object* v_i_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
size_t v_sz_boxed_1552_; size_t v_i_boxed_1553_; lean_object* v_res_1554_; 
v_sz_boxed_1552_ = lean_unbox_usize(v_sz_1542_);
lean_dec(v_sz_1542_);
v_i_boxed_1553_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_res_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_1539_, v_declName_1540_, v_as_1541_, v_sz_boxed_1552_, v_i_boxed_1553_, v_b_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v_as_1541_);
lean_dec_ref(v___x_1539_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___x_1558_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0));
v___x_1559_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1558_, v___x_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object* v_declName_1562_, uint8_t v_isMeta_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_env_1575_; lean_object* v___y_1577_; lean_object* v___x_1590_; 
v___x_1571_ = lean_st_ref_get(v___y_1569_);
v_env_1575_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_ref(v_env_1575_);
lean_dec(v___x_1571_);
v___x_1590_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1575_, v_declName_1562_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_dec_ref(v_env_1575_);
lean_dec(v_declName_1562_);
goto v___jp_1572_;
}
else
{
lean_object* v_val_1591_; lean_object* v___x_1592_; lean_object* v_modules_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = l_Lean_Environment_header(v_env_1575_);
v_modules_1593_ = lean_ctor_get(v___x_1592_, 3);
lean_inc_ref(v_modules_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = lean_array_get_size(v_modules_1593_);
v___x_1595_ = lean_nat_dec_lt(v_val_1591_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_dec_ref(v_modules_1593_);
lean_dec(v_val_1591_);
lean_dec_ref(v_env_1575_);
lean_dec(v_declName_1562_);
goto v___jp_1572_;
}
else
{
lean_object* v___x_1596_; lean_object* v_env_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___y_1601_; 
v___x_1596_ = lean_st_ref_get(v___y_1569_);
v_env_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_env_1597_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
v___x_1599_ = lean_array_fget(v_modules_1593_, v_val_1591_);
lean_dec(v_val_1591_);
lean_dec_ref(v_modules_1593_);
if (v_isMeta_1563_ == 0)
{
lean_dec_ref(v_env_1597_);
v___y_1601_ = v_isMeta_1563_;
goto v___jp_1600_;
}
else
{
uint8_t v___x_1612_; 
lean_inc(v_declName_1562_);
v___x_1612_ = l_Lean_isMarkedMeta(v_env_1597_, v_declName_1562_);
if (v___x_1612_ == 0)
{
v___y_1601_ = v_isMeta_1563_;
goto v___jp_1600_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = 0;
v___y_1601_ = v___x_1613_;
goto v___jp_1600_;
}
}
v___jp_1600_:
{
lean_object* v_toImport_1602_; lean_object* v_module_1603_; lean_object* v___x_1604_; 
v_toImport_1602_ = lean_ctor_get(v___x_1599_, 0);
lean_inc_ref(v_toImport_1602_);
lean_dec(v___x_1599_);
v_module_1603_ = lean_ctor_get(v_toImport_1602_, 0);
lean_inc(v_module_1603_);
lean_dec_ref(v_toImport_1602_);
lean_inc(v_declName_1562_);
v___x_1604_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1603_, v___y_1601_, v_declName_1562_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1604_, 1);
v___x_1605_ = l_Lean_indirectModUseExt;
v___x_1606_ = lean_box(1);
v___x_1607_ = lean_box(0);
lean_inc_ref(v_env_1575_);
v___x_1608_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1598_, v___x_1605_, v_env_1575_, v___x_1606_, v___x_1607_);
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_1608_, v_declName_1562_);
lean_dec(v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3));
v___y_1577_ = v___x_1610_;
goto v___jp_1576_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v___x_1609_, 1);
v___y_1577_ = v_val_1611_;
goto v___jp_1576_;
}
}
else
{
lean_dec_ref(v_env_1575_);
lean_dec(v_declName_1562_);
return v___x_1604_;
}
}
}
}
v___jp_1572_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
v___jp_1576_:
{
lean_object* v___x_1578_; size_t v_sz_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = lean_box(0);
v_sz_1579_ = lean_array_size(v___y_1577_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_1575_, v_declName_1562_, v___y_1577_, v_sz_1579_, v___x_1580_, v___x_1578_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec_ref(v___y_1577_);
lean_dec_ref(v_env_1575_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v___x_1581_, 0);
lean_dec(v_unused_1589_);
v___x_1583_ = v___x_1581_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v___x_1581_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1578_);
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1578_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
else
{
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object* v_declName_1614_, lean_object* v_isMeta_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v_isMeta_boxed_1623_; lean_object* v_res_1624_; 
v_isMeta_boxed_1623_ = lean_unbox(v_isMeta_1615_);
v_res_1624_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_1614_, v_isMeta_boxed_1623_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object* v_as_x27_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (lean_obj_tag(v_as_x27_1625_) == 0)
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_b_1626_);
return v___x_1634_;
}
else
{
lean_object* v_head_1635_; lean_object* v_tail_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v_head_1635_ = lean_ctor_get(v_as_x27_1625_, 0);
v_tail_1636_ = lean_ctor_get(v_as_x27_1625_, 1);
v___x_1637_ = 1;
lean_inc(v_head_1635_);
v___x_1638_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_1635_, v___x_1637_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref_known(v___x_1638_, 1);
v___x_1639_ = lean_box(0);
v_as_x27_1625_ = v_tail_1636_;
v_b_1626_ = v___x_1639_;
goto _start;
}
else
{
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_1641_, v_b_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v_as_x27_1641_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object* v_env_1651_, lean_object* v_currNamespace_1652_, lean_object* v_openDecls_1653_, lean_object* v_n_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = l_Lean_ResolveName_resolveNamespace(v_env_1651_, v_currNamespace_1652_, v_openDecls_1653_, v_n_1654_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___y_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object* v_env_1659_, lean_object* v_currNamespace_1660_, lean_object* v_openDecls_1661_, lean_object* v_n_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_1659_, v_currNamespace_1660_, v_openDecls_1661_, v_n_1662_, v___y_1663_, v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1665_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_box(1);
v___x_1667_ = l_Lean_MessageData_ofFormat(v___x_1666_);
return v___x_1667_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2));
v___x_1672_ = l_Lean_MessageData_ofFormat(v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
if (lean_obj_tag(v_x_1674_) == 0)
{
return v_x_1673_;
}
else
{
lean_object* v_head_1675_; lean_object* v_tail_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1698_; 
v_head_1675_ = lean_ctor_get(v_x_1674_, 0);
v_tail_1676_ = lean_ctor_get(v_x_1674_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1674_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1678_ = v_x_1674_;
v_isShared_1679_ = v_isSharedCheck_1698_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_tail_1676_);
lean_inc(v_head_1675_);
lean_dec(v_x_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1698_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_before_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1696_; 
v_before_1680_ = lean_ctor_get(v_head_1675_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_head_1675_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_head_1675_, 1);
lean_dec(v_unused_1697_);
v___x_1682_ = v_head_1675_;
v_isShared_1683_ = v_isSharedCheck_1696_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_before_1680_);
lean_dec(v_head_1675_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1696_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 7);
lean_ctor_set(v___x_1682_, 1, v___x_1684_);
lean_ctor_set(v___x_1682_, 0, v_x_1673_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_x_1673_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 7);
lean_ctor_set(v___x_1678_, 1, v___x_1687_);
lean_ctor_set(v___x_1678_, 0, v___x_1686_);
v___x_1689_ = v___x_1678_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = l_Lean_MessageData_ofSyntax(v_before_1680_);
v___x_1691_ = l_Lean_indentD(v___x_1690_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v_x_1673_ = v___x_1692_;
v_x_1674_ = v_tail_1676_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(lean_object* v_opts_1699_, lean_object* v_opt_1700_){
_start:
{
lean_object* v_name_1701_; lean_object* v_defValue_1702_; lean_object* v_map_1703_; lean_object* v___x_1704_; 
v_name_1701_ = lean_ctor_get(v_opt_1700_, 0);
v_defValue_1702_ = lean_ctor_get(v_opt_1700_, 1);
v_map_1703_ = lean_ctor_get(v_opts_1699_, 0);
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1703_, v_name_1701_);
if (lean_obj_tag(v___x_1704_) == 0)
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_unbox(v_defValue_1702_);
return v___x_1705_;
}
else
{
lean_object* v_val_1706_; 
v_val_1706_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_val_1706_);
lean_dec_ref_known(v___x_1704_, 1);
if (lean_obj_tag(v_val_1706_) == 1)
{
uint8_t v_v_1707_; 
v_v_1707_ = lean_ctor_get_uint8(v_val_1706_, 0);
lean_dec_ref_known(v_val_1706_, 0);
return v_v_1707_;
}
else
{
uint8_t v___x_1708_; 
lean_dec(v_val_1706_);
v___x_1708_ = lean_unbox(v_defValue_1702_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(lean_object* v_opts_1709_, lean_object* v_opt_1710_){
_start:
{
uint8_t v_res_1711_; lean_object* v_r_1712_; 
v_res_1711_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_1709_, v_opt_1710_);
lean_dec_ref(v_opt_1710_);
lean_dec_ref(v_opts_1709_);
v_r_1712_ = lean_box(v_res_1711_);
return v_r_1712_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1));
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(lean_object* v_msgData_1718_, lean_object* v_macroStack_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_options_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_options_1722_ = lean_ctor_get(v___y_1720_, 1);
v___x_1723_ = l_Lean_Elab_pp_macroStack;
v___x_1724_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_dec(v_macroStack_1719_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_msgData_1718_);
return v___x_1725_;
}
else
{
if (lean_obj_tag(v_macroStack_1719_) == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_msgData_1718_);
return v___x_1726_;
}
else
{
lean_object* v_head_1727_; lean_object* v_after_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1743_; 
v_head_1727_ = lean_ctor_get(v_macroStack_1719_, 0);
lean_inc(v_head_1727_);
v_after_1728_ = lean_ctor_get(v_head_1727_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_head_1727_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v_head_1727_, 0);
lean_dec(v_unused_1744_);
v___x_1730_ = v_head_1727_;
v_isShared_1731_ = v_isSharedCheck_1743_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_after_1728_);
lean_dec(v_head_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1743_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1731_ == 0)
{
lean_ctor_set_tag(v___x_1730_, 7);
lean_ctor_set(v___x_1730_, 1, v___x_1732_);
lean_ctor_set(v___x_1730_, 0, v_msgData_1718_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_msgData_1718_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_msgData_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1735_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_MessageData_ofSyntax(v_after_1728_);
v___x_1738_ = l_Lean_indentD(v___x_1737_);
v_msgData_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1739_, 0, v___x_1736_);
lean_ctor_set(v_msgData_1739_, 1, v___x_1738_);
v___x_1740_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_1739_, v_macroStack_1719_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(lean_object* v_msgData_1745_, lean_object* v_macroStack_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_1745_, v_macroStack_1746_, v___y_1747_);
lean_dec_ref(v___y_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_ref_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v_macroStack_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
v_ref_1758_ = lean_ctor_get(v___y_1755_, 4);
v___x_1759_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1750_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v_macroStack_1761_ = lean_ctor_get(v___y_1751_, 1);
v___x_1762_ = l_Lean_Elab_getBetterRef(v_ref_1758_, v_macroStack_1761_);
lean_inc(v_macroStack_1761_);
v___x_1763_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_1760_, v_macroStack_1761_, v___y_1755_);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1762_);
lean_ctor_set(v___x_1768_, 1, v_a_1764_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set_tag(v___x_1766_, 1);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(lean_object* v_ref_1782_, lean_object* v_msg_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_toCold_1791_; lean_object* v_options_1792_; lean_object* v_currRecDepth_1793_; lean_object* v_maxRecDepth_1794_; lean_object* v_ref_1795_; lean_object* v_currNamespace_1796_; lean_object* v_openDecls_1797_; lean_object* v_initHeartbeats_1798_; lean_object* v_maxHeartbeats_1799_; lean_object* v_currMacroScope_1800_; uint8_t v_diag_1801_; uint8_t v_suppressElabErrors_1802_; lean_object* v_ref_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_toCold_1791_ = lean_ctor_get(v___y_1788_, 0);
v_options_1792_ = lean_ctor_get(v___y_1788_, 1);
v_currRecDepth_1793_ = lean_ctor_get(v___y_1788_, 2);
v_maxRecDepth_1794_ = lean_ctor_get(v___y_1788_, 3);
v_ref_1795_ = lean_ctor_get(v___y_1788_, 4);
v_currNamespace_1796_ = lean_ctor_get(v___y_1788_, 5);
v_openDecls_1797_ = lean_ctor_get(v___y_1788_, 6);
v_initHeartbeats_1798_ = lean_ctor_get(v___y_1788_, 7);
v_maxHeartbeats_1799_ = lean_ctor_get(v___y_1788_, 8);
v_currMacroScope_1800_ = lean_ctor_get(v___y_1788_, 9);
v_diag_1801_ = lean_ctor_get_uint8(v___y_1788_, sizeof(void*)*10);
v_suppressElabErrors_1802_ = lean_ctor_get_uint8(v___y_1788_, sizeof(void*)*10 + 1);
v_ref_1803_ = l_Lean_replaceRef(v_ref_1782_, v_ref_1795_);
lean_inc(v_currMacroScope_1800_);
lean_inc(v_maxHeartbeats_1799_);
lean_inc(v_initHeartbeats_1798_);
lean_inc(v_openDecls_1797_);
lean_inc(v_currNamespace_1796_);
lean_inc(v_maxRecDepth_1794_);
lean_inc(v_currRecDepth_1793_);
lean_inc_ref(v_options_1792_);
lean_inc_ref(v_toCold_1791_);
v___x_1804_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1804_, 0, v_toCold_1791_);
lean_ctor_set(v___x_1804_, 1, v_options_1792_);
lean_ctor_set(v___x_1804_, 2, v_currRecDepth_1793_);
lean_ctor_set(v___x_1804_, 3, v_maxRecDepth_1794_);
lean_ctor_set(v___x_1804_, 4, v_ref_1803_);
lean_ctor_set(v___x_1804_, 5, v_currNamespace_1796_);
lean_ctor_set(v___x_1804_, 6, v_openDecls_1797_);
lean_ctor_set(v___x_1804_, 7, v_initHeartbeats_1798_);
lean_ctor_set(v___x_1804_, 8, v_maxHeartbeats_1799_);
lean_ctor_set(v___x_1804_, 9, v_currMacroScope_1800_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*10, v_diag_1801_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*10 + 1, v_suppressElabErrors_1802_);
v___x_1805_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___x_1804_, v___y_1789_);
lean_dec_ref_known(v___x_1804_, 10);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1806_, lean_object* v_msg_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_1806_, v_msg_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v_ref_1806_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; lean_object* v_toCold_1826_; lean_object* v_env_1827_; lean_object* v_options_1828_; lean_object* v_currRecDepth_1829_; lean_object* v_maxRecDepth_1830_; lean_object* v_ref_1831_; lean_object* v_currNamespace_1832_; lean_object* v_openDecls_1833_; lean_object* v_currMacroScope_1834_; lean_object* v_quotContext_1835_; lean_object* v___x_1836_; lean_object* v_nextMacroScope_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v_methods_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1825_ = lean_st_ref_get(v___y_1823_);
v_toCold_1826_ = lean_ctor_get(v___y_1822_, 0);
v_env_1827_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref_n(v_env_1827_, 4);
lean_dec(v___x_1825_);
v_options_1828_ = lean_ctor_get(v___y_1822_, 1);
v_currRecDepth_1829_ = lean_ctor_get(v___y_1822_, 2);
v_maxRecDepth_1830_ = lean_ctor_get(v___y_1822_, 3);
v_ref_1831_ = lean_ctor_get(v___y_1822_, 4);
v_currNamespace_1832_ = lean_ctor_get(v___y_1822_, 5);
v_openDecls_1833_ = lean_ctor_get(v___y_1822_, 6);
v_currMacroScope_1834_ = lean_ctor_get(v___y_1822_, 9);
v_quotContext_1835_ = lean_ctor_get(v_toCold_1826_, 2);
v___x_1836_ = lean_st_ref_get(v___y_1823_);
v_nextMacroScope_1837_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_nextMacroScope_1837_);
lean_dec(v___x_1836_);
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1838_, 0, v_env_1827_);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1839_, 0, v_env_1827_);
lean_inc_n(v_openDecls_1833_, 2);
lean_inc_n(v_currNamespace_1832_, 3);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1840_, 0, v_env_1827_);
lean_closure_set(v___f_1840_, 1, v_currNamespace_1832_);
lean_closure_set(v___f_1840_, 2, v_openDecls_1833_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1841_, 0, v_currNamespace_1832_);
lean_inc_ref(v_options_1828_);
v___f_1842_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1842_, 0, v_env_1827_);
lean_closure_set(v___f_1842_, 1, v_options_1828_);
lean_closure_set(v___f_1842_, 2, v_currNamespace_1832_);
lean_closure_set(v___f_1842_, 3, v_openDecls_1833_);
v_methods_1843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1843_, 0, v___f_1838_);
lean_ctor_set(v_methods_1843_, 1, v___f_1841_);
lean_ctor_set(v_methods_1843_, 2, v___f_1839_);
lean_ctor_set(v_methods_1843_, 3, v___f_1840_);
lean_ctor_set(v_methods_1843_, 4, v___f_1842_);
lean_inc(v_ref_1831_);
lean_inc(v_maxRecDepth_1830_);
lean_inc(v_currRecDepth_1829_);
lean_inc(v_currMacroScope_1834_);
lean_inc(v_quotContext_1835_);
v___x_1844_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1844_, 0, v_methods_1843_);
lean_ctor_set(v___x_1844_, 1, v_quotContext_1835_);
lean_ctor_set(v___x_1844_, 2, v_currMacroScope_1834_);
lean_ctor_set(v___x_1844_, 3, v_currRecDepth_1829_);
lean_ctor_set(v___x_1844_, 4, v_maxRecDepth_1830_);
lean_ctor_set(v___x_1844_, 5, v_ref_1831_);
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1846_, 0, v_nextMacroScope_1837_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
lean_ctor_set(v___x_1846_, 2, v___x_1845_);
v___x_1847_ = lean_apply_2(v_x_1817_, v___x_1844_, v___x_1846_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_a_1849_; lean_object* v_macroScope_1850_; lean_object* v_traceMsgs_1851_; lean_object* v_expandedMacroDecls_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_a_1848_);
v_a_1849_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1847_, 2);
v_macroScope_1850_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_macroScope_1850_);
v_traceMsgs_1851_ = lean_ctor_get(v_a_1848_, 1);
lean_inc(v_traceMsgs_1851_);
v_expandedMacroDecls_1852_ = lean_ctor_get(v_a_1848_, 2);
lean_inc(v_expandedMacroDecls_1852_);
lean_dec(v_a_1848_);
v___x_1853_ = lean_box(0);
v___x_1854_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_1852_, v___x_1853_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v_expandedMacroDecls_1852_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v___x_1855_; lean_object* v_env_1856_; lean_object* v_ngen_1857_; lean_object* v_auxDeclNGen_1858_; lean_object* v_traceState_1859_; lean_object* v_cache_1860_; lean_object* v_messages_1861_; lean_object* v_infoState_1862_; lean_object* v_snapshotTasks_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref_known(v___x_1854_, 1);
v___x_1855_ = lean_st_ref_take(v___y_1823_);
v_env_1856_ = lean_ctor_get(v___x_1855_, 0);
v_ngen_1857_ = lean_ctor_get(v___x_1855_, 2);
v_auxDeclNGen_1858_ = lean_ctor_get(v___x_1855_, 3);
v_traceState_1859_ = lean_ctor_get(v___x_1855_, 4);
v_cache_1860_ = lean_ctor_get(v___x_1855_, 5);
v_messages_1861_ = lean_ctor_get(v___x_1855_, 6);
v_infoState_1862_ = lean_ctor_get(v___x_1855_, 7);
v_snapshotTasks_1863_ = lean_ctor_get(v___x_1855_, 8);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1855_, 1);
lean_dec(v_unused_1890_);
v___x_1865_ = v___x_1855_;
v_isShared_1866_ = v_isSharedCheck_1889_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snapshotTasks_1863_);
lean_inc(v_infoState_1862_);
lean_inc(v_messages_1861_);
lean_inc(v_cache_1860_);
lean_inc(v_traceState_1859_);
lean_inc(v_auxDeclNGen_1858_);
lean_inc(v_ngen_1857_);
lean_inc(v_env_1856_);
lean_dec(v___x_1855_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1889_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v_macroScope_1850_);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_env_1856_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_macroScope_1850_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_ngen_1857_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_auxDeclNGen_1858_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_traceState_1859_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_cache_1860_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_messages_1861_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_infoState_1862_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_snapshotTasks_1863_);
v___x_1868_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_st_ref_put(v___y_1823_, v___x_1868_);
v___x_1870_ = l_List_reverse___redArg(v_traceMsgs_1851_);
v___x_1871_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_1870_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1871_, 0);
lean_dec(v_unused_1879_);
v___x_1873_ = v___x_1871_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_dec(v___x_1871_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_a_1849_);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1849_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_a_1849_);
v_a_1880_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1871_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1871_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_traceMsgs_1851_);
lean_dec(v_macroScope_1850_);
lean_dec(v_a_1849_);
v_a_1891_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1854_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1854_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1847_, 2);
if (lean_obj_tag(v_a_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v_a_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_a_1900_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_a_1900_);
v_a_1901_ = lean_ctor_get(v_a_1899_, 1);
lean_inc_ref(v_a_1901_);
lean_dec_ref_known(v_a_1899_, 2);
v___x_1902_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0));
v___x_1903_ = lean_string_dec_eq(v_a_1901_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1901_);
v___x_1905_ = l_Lean_MessageData_ofFormat(v___x_1904_);
v___x_1906_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_1900_, v___x_1905_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v_a_1900_);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; 
lean_dec_ref(v_a_1901_);
v___x_1907_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_1900_);
return v___x_1907_;
}
}
else
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* v_x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(lean_object* v_t_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; lean_object* v_infoState_1922_; uint8_t v_enabled_1923_; 
v___x_1921_ = lean_st_ref_get(v___y_1919_);
v_infoState_1922_ = lean_ctor_get(v___x_1921_, 7);
lean_inc_ref(v_infoState_1922_);
lean_dec(v___x_1921_);
v_enabled_1923_ = lean_ctor_get_uint8(v_infoState_1922_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1922_);
if (v_enabled_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v_t_1918_);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v_infoState_1927_; lean_object* v_env_1928_; lean_object* v_nextMacroScope_1929_; lean_object* v_ngen_1930_; lean_object* v_auxDeclNGen_1931_; lean_object* v_traceState_1932_; lean_object* v_cache_1933_; lean_object* v_messages_1934_; lean_object* v_snapshotTasks_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1957_; 
v___x_1926_ = lean_st_ref_take(v___y_1919_);
v_infoState_1927_ = lean_ctor_get(v___x_1926_, 7);
v_env_1928_ = lean_ctor_get(v___x_1926_, 0);
v_nextMacroScope_1929_ = lean_ctor_get(v___x_1926_, 1);
v_ngen_1930_ = lean_ctor_get(v___x_1926_, 2);
v_auxDeclNGen_1931_ = lean_ctor_get(v___x_1926_, 3);
v_traceState_1932_ = lean_ctor_get(v___x_1926_, 4);
v_cache_1933_ = lean_ctor_get(v___x_1926_, 5);
v_messages_1934_ = lean_ctor_get(v___x_1926_, 6);
v_snapshotTasks_1935_ = lean_ctor_get(v___x_1926_, 8);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1937_ = v___x_1926_;
v_isShared_1938_ = v_isSharedCheck_1957_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_snapshotTasks_1935_);
lean_inc(v_infoState_1927_);
lean_inc(v_messages_1934_);
lean_inc(v_cache_1933_);
lean_inc(v_traceState_1932_);
lean_inc(v_auxDeclNGen_1931_);
lean_inc(v_ngen_1930_);
lean_inc(v_nextMacroScope_1929_);
lean_inc(v_env_1928_);
lean_dec(v___x_1926_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1957_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
uint8_t v_enabled_1939_; lean_object* v_assignment_1940_; lean_object* v_lazyAssignment_1941_; lean_object* v_trees_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1956_; 
v_enabled_1939_ = lean_ctor_get_uint8(v_infoState_1927_, sizeof(void*)*3);
v_assignment_1940_ = lean_ctor_get(v_infoState_1927_, 0);
v_lazyAssignment_1941_ = lean_ctor_get(v_infoState_1927_, 1);
v_trees_1942_ = lean_ctor_get(v_infoState_1927_, 2);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_infoState_1927_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1944_ = v_infoState_1927_;
v_isShared_1945_ = v_isSharedCheck_1956_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_trees_1942_);
lean_inc(v_lazyAssignment_1941_);
lean_inc(v_assignment_1940_);
lean_dec(v_infoState_1927_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1956_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_PersistentArray_push___redArg(v_trees_1942_, v_t_1918_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 2, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_assignment_1940_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_lazyAssignment_1941_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v___x_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*3, v_enabled_1939_);
v___x_1948_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 7, v___x_1948_);
v___x_1950_ = v___x_1937_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_env_1928_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_nextMacroScope_1929_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_ngen_1930_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_auxDeclNGen_1931_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_traceState_1932_);
lean_ctor_set(v_reuseFailAlloc_1954_, 5, v_cache_1933_);
lean_ctor_set(v_reuseFailAlloc_1954_, 6, v_messages_1934_);
lean_ctor_set(v_reuseFailAlloc_1954_, 7, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1954_, 8, v_snapshotTasks_1935_);
v___x_1950_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_st_ref_put(v___y_1919_, v___x_1950_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(lean_object* v_t_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_1958_, v___y_1959_);
lean_dec(v___y_1959_);
return v_res_1961_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_unsigned_to_nat(32u);
v___x_1963_ = lean_mk_empty_array_with_capacity(v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1(void){
_start:
{
size_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1965_ = ((size_t)5ULL);
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_unsigned_to_nat(32u);
v___x_1968_ = lean_mk_empty_array_with_capacity(v___x_1967_);
v___x_1969_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
v___x_1970_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___x_1968_);
lean_ctor_set(v___x_1970_, 2, v___x_1966_);
lean_ctor_set(v___x_1970_, 3, v___x_1966_);
lean_ctor_set_usize(v___x_1970_, 4, v___x_1965_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object* v_t_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; lean_object* v_infoState_1980_; uint8_t v_enabled_1981_; 
v___x_1979_ = lean_st_ref_get(v___y_1977_);
v_infoState_1980_ = lean_ctor_get(v___x_1979_, 7);
lean_inc_ref(v_infoState_1980_);
lean_dec(v___x_1979_);
v_enabled_1981_ = lean_ctor_get_uint8(v_infoState_1980_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1980_);
if (v_enabled_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_t_1971_);
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_t_1971_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_1985_, v___y_1977_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object* v_t_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v_t_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object* v_info_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_info_1996_);
v___x_2005_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2004_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object* v_info_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_2022_, uint8_t v___y_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 1)
{
lean_object* v_pre_2025_; 
v_pre_2025_ = lean_ctor_get(v_x_2024_, 0);
switch(lean_obj_tag(v_pre_2025_))
{
case 1:
{
lean_object* v_pre_2026_; 
v_pre_2026_ = lean_ctor_get(v_pre_2025_, 0);
switch(lean_obj_tag(v_pre_2026_))
{
case 0:
{
lean_object* v_str_2027_; lean_object* v_str_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_str_2027_ = lean_ctor_get(v_x_2024_, 1);
v_str_2028_ = lean_ctor_get(v_pre_2025_, 1);
v___x_2029_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0));
v___x_2030_ = lean_string_dec_eq(v_str_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1));
v___x_2032_ = lean_string_dec_eq(v_str_2028_, v___x_2031_);
if (v___x_2032_ == 0)
{
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2));
v___x_2034_ = lean_string_dec_eq(v_str_2027_, v___x_2033_);
if (v___x_2034_ == 0)
{
return v___x_2034_;
}
else
{
return v_suppressElabErrors_2022_;
}
}
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3));
v___x_2036_ = lean_string_dec_eq(v_str_2027_, v___x_2035_);
if (v___x_2036_ == 0)
{
return v___x_2036_;
}
else
{
return v_suppressElabErrors_2022_;
}
}
}
case 1:
{
lean_object* v_pre_2037_; 
v_pre_2037_ = lean_ctor_get(v_pre_2026_, 0);
if (lean_obj_tag(v_pre_2037_) == 0)
{
lean_object* v_str_2038_; lean_object* v_str_2039_; lean_object* v_str_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_str_2038_ = lean_ctor_get(v_x_2024_, 1);
v_str_2039_ = lean_ctor_get(v_pre_2025_, 1);
v_str_2040_ = lean_ctor_get(v_pre_2026_, 1);
v___x_2041_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4));
v___x_2042_ = lean_string_dec_eq(v_str_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5));
v___x_2044_ = lean_string_dec_eq(v_str_2039_, v___x_2043_);
if (v___x_2044_ == 0)
{
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6));
v___x_2046_ = lean_string_dec_eq(v_str_2038_, v___x_2045_);
if (v___x_2046_ == 0)
{
return v___x_2046_;
}
else
{
return v_suppressElabErrors_2022_;
}
}
}
}
else
{
return v___y_2023_;
}
}
default: 
{
return v___y_2023_;
}
}
}
case 0:
{
lean_object* v_str_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_str_2047_ = lean_ctor_get(v_x_2024_, 1);
v___x_2048_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0));
v___x_2049_ = lean_string_dec_eq(v_str_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
return v___x_2049_;
}
else
{
return v_suppressElabErrors_2022_;
}
}
default: 
{
return v___y_2023_;
}
}
}
else
{
return v___y_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2050_, lean_object* v___y_2051_, lean_object* v_x_2052_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2053_; uint8_t v___y_21569__boxed_2054_; uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_suppressElabErrors_boxed_2053_ = lean_unbox(v_suppressElabErrors_2050_);
v___y_21569__boxed_2054_ = lean_unbox(v___y_2051_);
v_res_2055_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_2053_, v___y_21569__boxed_2054_, v_x_2052_);
lean_dec(v_x_2052_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(lean_object* v_ref_2057_, lean_object* v_msgData_2058_, uint8_t v_severity_2059_, uint8_t v_isSilent_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___y_2067_; lean_object* v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; uint8_t v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; uint8_t v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; uint8_t v___y_2132_; uint8_t v___y_2133_; uint8_t v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2139_; lean_object* v___y_2140_; uint8_t v___y_2141_; lean_object* v___y_2142_; uint8_t v___y_2143_; uint8_t v___y_2144_; uint8_t v___x_2149_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; uint8_t v___y_2154_; uint8_t v___y_2155_; uint8_t v___y_2156_; uint8_t v___y_2158_; uint8_t v___x_2172_; 
v___x_2149_ = 2;
v___x_2172_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2059_, v___x_2149_);
if (v___x_2172_ == 0)
{
v___y_2158_ = v___x_2172_;
goto v___jp_2157_;
}
else
{
uint8_t v___x_2173_; 
lean_inc_ref(v_msgData_2058_);
v___x_2173_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2058_);
v___y_2158_ = v___x_2173_;
goto v___jp_2157_;
}
v___jp_2066_:
{
lean_object* v___x_2076_; lean_object* v_currNamespace_2077_; lean_object* v_openDecls_2078_; lean_object* v_env_2079_; lean_object* v_nextMacroScope_2080_; lean_object* v_ngen_2081_; lean_object* v_auxDeclNGen_2082_; lean_object* v_traceState_2083_; lean_object* v_cache_2084_; lean_object* v_messages_2085_; lean_object* v_infoState_2086_; lean_object* v_snapshotTasks_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2101_; 
v___x_2076_ = lean_st_ref_take(v___y_2075_);
v_currNamespace_2077_ = lean_ctor_get(v___y_2074_, 5);
v_openDecls_2078_ = lean_ctor_get(v___y_2074_, 6);
v_env_2079_ = lean_ctor_get(v___x_2076_, 0);
v_nextMacroScope_2080_ = lean_ctor_get(v___x_2076_, 1);
v_ngen_2081_ = lean_ctor_get(v___x_2076_, 2);
v_auxDeclNGen_2082_ = lean_ctor_get(v___x_2076_, 3);
v_traceState_2083_ = lean_ctor_get(v___x_2076_, 4);
v_cache_2084_ = lean_ctor_get(v___x_2076_, 5);
v_messages_2085_ = lean_ctor_get(v___x_2076_, 6);
v_infoState_2086_ = lean_ctor_get(v___x_2076_, 7);
v_snapshotTasks_2087_ = lean_ctor_get(v___x_2076_, 8);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2089_ = v___x_2076_;
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_snapshotTasks_2087_);
lean_inc(v_infoState_2086_);
lean_inc(v_messages_2085_);
lean_inc(v_cache_2084_);
lean_inc(v_traceState_2083_);
lean_inc(v_auxDeclNGen_2082_);
lean_inc(v_ngen_2081_);
lean_inc(v_nextMacroScope_2080_);
lean_inc(v_env_2079_);
lean_dec(v___x_2076_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_inc(v_openDecls_2078_);
lean_inc(v_currNamespace_2077_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_currNamespace_2077_);
lean_ctor_set(v___x_2091_, 1, v_openDecls_2078_);
v___x_2092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___y_2073_);
lean_inc_ref(v___y_2070_);
lean_inc_ref(v___y_2067_);
v___x_2093_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2093_, 0, v___y_2067_);
lean_ctor_set(v___x_2093_, 1, v___y_2071_);
lean_ctor_set(v___x_2093_, 2, v___y_2068_);
lean_ctor_set(v___x_2093_, 3, v___y_2070_);
lean_ctor_set(v___x_2093_, 4, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*5, v___y_2069_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*5 + 1, v___y_2072_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*5 + 2, v_isSilent_2060_);
v___x_2094_ = l_Lean_MessageLog_add(v___x_2093_, v_messages_2085_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 6, v___x_2094_);
v___x_2096_ = v___x_2089_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_env_2079_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_nextMacroScope_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_ngen_2081_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_auxDeclNGen_2082_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_traceState_2083_);
lean_ctor_set(v_reuseFailAlloc_2100_, 5, v_cache_2084_);
lean_ctor_set(v_reuseFailAlloc_2100_, 6, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2100_, 7, v_infoState_2086_);
lean_ctor_set(v_reuseFailAlloc_2100_, 8, v_snapshotTasks_2087_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_st_ref_put(v___y_2075_, v___x_2096_);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
}
v___jp_2102_:
{
lean_object* v_fileName_2110_; lean_object* v_fileMap_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2127_; 
v_fileName_2110_ = lean_ctor_get(v___y_2104_, 0);
v_fileMap_2111_ = lean_ctor_get(v___y_2104_, 1);
v___x_2112_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2058_);
v___x_2113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_2112_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2127_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2127_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_inc_ref_n(v_fileMap_2111_, 2);
v___x_2118_ = l_Lean_FileMap_toPosition(v_fileMap_2111_, v___y_2106_);
lean_dec(v___y_2106_);
v___x_2119_ = l_Lean_FileMap_toPosition(v_fileMap_2111_, v___y_2109_);
lean_dec(v___y_2109_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
v___x_2121_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
if (v___y_2108_ == 0)
{
lean_del_object(v___x_2116_);
lean_dec_ref(v___y_2103_);
v___y_2067_ = v_fileName_2110_;
v___y_2068_ = v___x_2120_;
v___y_2069_ = v___y_2105_;
v___y_2070_ = v___x_2121_;
v___y_2071_ = v___x_2118_;
v___y_2072_ = v___y_2107_;
v___y_2073_ = v_a_2114_;
v___y_2074_ = v___y_2063_;
v___y_2075_ = v___y_2064_;
goto v___jp_2066_;
}
else
{
uint8_t v___x_2122_; 
lean_inc(v_a_2114_);
v___x_2122_ = l_Lean_MessageData_hasTag(v___y_2103_, v_a_2114_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec_ref_known(v___x_2120_, 1);
lean_dec_ref(v___x_2118_);
lean_dec(v_a_2114_);
v___x_2123_ = lean_box(0);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2123_);
v___x_2125_ = v___x_2116_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
lean_del_object(v___x_2116_);
v___y_2067_ = v_fileName_2110_;
v___y_2068_ = v___x_2120_;
v___y_2069_ = v___y_2105_;
v___y_2070_ = v___x_2121_;
v___y_2071_ = v___x_2118_;
v___y_2072_ = v___y_2107_;
v___y_2073_ = v_a_2114_;
v___y_2074_ = v___y_2063_;
v___y_2075_ = v___y_2064_;
goto v___jp_2066_;
}
}
}
}
v___jp_2128_:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Syntax_getTailPos_x3f(v___y_2130_, v___y_2132_);
lean_dec(v___y_2130_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_inc(v___y_2135_);
v___y_2103_ = v___y_2129_;
v___y_2104_ = v___y_2131_;
v___y_2105_ = v___y_2132_;
v___y_2106_ = v___y_2135_;
v___y_2107_ = v___y_2133_;
v___y_2108_ = v___y_2134_;
v___y_2109_ = v___y_2135_;
goto v___jp_2102_;
}
else
{
lean_object* v_val_2137_; 
v_val_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___y_2103_ = v___y_2129_;
v___y_2104_ = v___y_2131_;
v___y_2105_ = v___y_2132_;
v___y_2106_ = v___y_2135_;
v___y_2107_ = v___y_2133_;
v___y_2108_ = v___y_2134_;
v___y_2109_ = v_val_2137_;
goto v___jp_2102_;
}
}
v___jp_2138_:
{
lean_object* v_ref_2145_; lean_object* v___x_2146_; 
v_ref_2145_ = l_Lean_replaceRef(v_ref_2057_, v___y_2142_);
v___x_2146_ = l_Lean_Syntax_getPos_x3f(v_ref_2145_, v___y_2141_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___y_2129_ = v___y_2139_;
v___y_2130_ = v_ref_2145_;
v___y_2131_ = v___y_2140_;
v___y_2132_ = v___y_2141_;
v___y_2133_ = v___y_2144_;
v___y_2134_ = v___y_2143_;
v___y_2135_ = v___x_2147_;
goto v___jp_2128_;
}
else
{
lean_object* v_val_2148_; 
v_val_2148_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_val_2148_);
lean_dec_ref_known(v___x_2146_, 1);
v___y_2129_ = v___y_2139_;
v___y_2130_ = v_ref_2145_;
v___y_2131_ = v___y_2140_;
v___y_2132_ = v___y_2141_;
v___y_2133_ = v___y_2144_;
v___y_2134_ = v___y_2143_;
v___y_2135_ = v_val_2148_;
goto v___jp_2128_;
}
}
v___jp_2150_:
{
if (v___y_2156_ == 0)
{
v___y_2139_ = v___y_2152_;
v___y_2140_ = v___y_2151_;
v___y_2141_ = v___y_2155_;
v___y_2142_ = v___y_2153_;
v___y_2143_ = v___y_2154_;
v___y_2144_ = v_severity_2059_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v___y_2152_;
v___y_2140_ = v___y_2151_;
v___y_2141_ = v___y_2155_;
v___y_2142_ = v___y_2153_;
v___y_2143_ = v___y_2154_;
v___y_2144_ = v___x_2149_;
goto v___jp_2138_;
}
}
v___jp_2157_:
{
if (v___y_2158_ == 0)
{
lean_object* v_toCold_2159_; lean_object* v_options_2160_; lean_object* v_ref_2161_; uint8_t v_suppressElabErrors_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; 
v_toCold_2159_ = lean_ctor_get(v___y_2063_, 0);
v_options_2160_ = lean_ctor_get(v___y_2063_, 1);
v_ref_2161_ = lean_ctor_get(v___y_2063_, 4);
v_suppressElabErrors_2162_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*10 + 1);
v___x_2163_ = lean_box(v_suppressElabErrors_2162_);
v___x_2164_ = lean_box(v___y_2158_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2165_, 0, v___x_2163_);
lean_closure_set(v___f_2165_, 1, v___x_2164_);
v___x_2166_ = 1;
v___x_2167_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2059_, v___x_2166_);
if (v___x_2167_ == 0)
{
v___y_2151_ = v_toCold_2159_;
v___y_2152_ = v___f_2165_;
v___y_2153_ = v_ref_2161_;
v___y_2154_ = v_suppressElabErrors_2162_;
v___y_2155_ = v___y_2158_;
v___y_2156_ = v___x_2167_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = l_Lean_warningAsError;
v___x_2169_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_2160_, v___x_2168_);
v___y_2151_ = v_toCold_2159_;
v___y_2152_ = v___f_2165_;
v___y_2153_ = v_ref_2161_;
v___y_2154_ = v_suppressElabErrors_2162_;
v___y_2155_ = v___y_2158_;
v___y_2156_ = v___x_2169_;
goto v___jp_2150_;
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v_msgData_2058_);
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(lean_object* v_ref_2174_, lean_object* v_msgData_2175_, lean_object* v_severity_2176_, lean_object* v_isSilent_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v_severity_boxed_2183_; uint8_t v_isSilent_boxed_2184_; lean_object* v_res_2185_; 
v_severity_boxed_2183_ = lean_unbox(v_severity_2176_);
v_isSilent_boxed_2184_ = lean_unbox(v_isSilent_2177_);
v_res_2185_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2174_, v_msgData_2175_, v_severity_boxed_2183_, v_isSilent_boxed_2184_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_ref_2174_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object* v_ref_2186_, lean_object* v_msgData_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = 2;
v___x_2196_ = 0;
v___x_2197_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2186_, v_msgData_2187_, v___x_2195_, v___x_2196_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object* v_ref_2198_, lean_object* v_msgData_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v_ref_2198_, v_msgData_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v_ref_2198_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object* v_ref_2208_, lean_object* v_msgData_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = 1;
v___x_2218_ = 0;
v___x_2219_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2208_, v_msgData_2209_, v___x_2217_, v___x_2218_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object* v_ref_2220_, lean_object* v_msgData_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v_ref_2220_, v_msgData_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v_ref_2220_);
return v_res_2229_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* v_stx_2257_, lean_object* v_expType_x3f_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
uint8_t v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2287_; lean_object* v___y_2288_; uint8_t v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v_fst_2359_; lean_object* v_snd_2360_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; uint8_t v___y_2388_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_inc(v_stx_2257_);
v___x_2406_ = l_Lean_Syntax_getKind(v_stx_2257_);
v___x_2407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_2405_, v___x_2406_);
lean_dec(v___x_2406_);
if (lean_obj_tag(v___x_2407_) == 1)
{
lean_object* v_val_2408_; lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2441_; 
v_val_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v_fst_2409_ = lean_ctor_get(v_val_2408_, 0);
v_snd_2410_ = lean_ctor_get(v_val_2408_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_val_2408_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2412_ = v_val_2408_;
v_isShared_2413_ = v_isSharedCheck_2441_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snd_2410_);
lean_inc(v_fst_2409_);
lean_dec(v_val_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2441_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v_env_2415_; uint8_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2414_ = lean_st_ref_get(v_a_2264_);
v_env_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_env_2415_);
lean_dec(v___x_2414_);
v___x_2416_ = 1;
lean_inc(v_snd_2410_);
v___x_2417_ = l_Lean_Environment_contains(v_env_2415_, v_snd_2410_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
lean_dec(v_expType_x3f_2258_);
lean_dec(v_stx_2257_);
v___x_2418_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
v___x_2419_ = l_Lean_MessageData_ofName(v_snd_2410_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 7);
lean_ctor_set(v___x_2412_, 1, v___x_2419_);
lean_ctor_set(v___x_2412_, 0, v___x_2418_);
v___x_2421_ = v___x_2412_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v___x_2422_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
v___x_2425_ = l_Lean_MessageData_ofName(v_fst_2409_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
v___x_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = l_Lean_MessageData_hint_x27(v___x_2428_);
v___x_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2423_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_2430_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_del_object(v___x_2412_);
lean_dec(v_snd_2410_);
lean_dec(v_fst_2409_);
v___y_2395_ = v_a_2259_;
v___y_2396_ = v_a_2260_;
v___y_2397_ = v_a_2261_;
v___y_2398_ = v_a_2262_;
v___y_2399_ = v_a_2263_;
v___y_2400_ = v_a_2264_;
goto v___jp_2394_;
}
}
}
else
{
lean_dec(v___x_2407_);
v___y_2395_ = v_a_2259_;
v___y_2396_ = v_a_2260_;
v___y_2397_ = v_a_2261_;
v___y_2398_ = v_a_2262_;
v___y_2399_ = v_a_2263_;
v___y_2400_ = v_a_2264_;
goto v___jp_2394_;
}
v___jp_2266_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed), 3, 1);
lean_closure_set(v___x_2274_, 0, v_stx_2257_);
v___x_2275_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_2274_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___x_2277_ = l_Lean_Elab_Term_elabTerm(v_a_2276_, v_expType_x3f_2258_, v___y_2267_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2277_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_expType_x3f_2258_);
v_a_2278_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2275_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2275_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v___jp_2286_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_partialId_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2350_; 
v___x_2296_ = l_Lean_Syntax_getNumArgs(v___y_2295_);
v___x_2297_ = lean_unsigned_to_nat(2u);
v___x_2298_ = lean_nat_sub(v___x_2296_, v___x_2297_);
lean_dec(v___x_2296_);
v_partialId_2299_ = l_Lean_Syntax_getArg(v___y_2295_, v___x_2298_);
lean_dec(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___y_2295_);
lean_ctor_set(v___x_2300_, 1, v_partialId_2299_);
v___x_2301_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_2300_, v___y_2292_, v___y_2287_, v___y_2291_, v___y_2294_, v___y_2288_, v___y_2290_);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2351_);
v___x_2303_ = v___x_2301_;
v_isShared_2304_ = v_isSharedCheck_2350_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v___x_2301_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2350_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2305_ = l_Lean_Syntax_getId(v___y_2293_);
v___x_2306_ = l_Lean_Name_eraseMacroScopes(v___x_2305_);
lean_dec(v___x_2305_);
lean_inc(v___x_2306_);
lean_inc(v___y_2293_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___y_2293_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 6);
lean_ctor_set(v___x_2303_, 0, v___x_2307_);
v___x_2309_ = v___x_2303_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_a_2312_; 
v___x_2310_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2309_, v___y_2292_, v___y_2287_, v___y_2291_, v___y_2294_, v___y_2288_, v___y_2290_);
lean_dec_ref(v___x_2310_);
v___x_2311_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_2306_, v___y_2290_);
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
if (lean_obj_tag(v_a_2312_) == 1)
{
lean_object* v_val_2313_; lean_object* v_metadata_2314_; lean_object* v_removedVersion_x3f_2315_; 
v_val_2313_ = lean_ctor_get(v_a_2312_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v_a_2312_, 1);
v_metadata_2314_ = lean_ctor_get(v_val_2313_, 1);
lean_inc_ref(v_metadata_2314_);
lean_dec(v_val_2313_);
v_removedVersion_x3f_2315_ = lean_ctor_get(v_metadata_2314_, 2);
lean_inc(v_removedVersion_x3f_2315_);
lean_dec_ref(v_metadata_2314_);
if (lean_obj_tag(v_removedVersion_x3f_2315_) == 1)
{
lean_object* v_val_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_val_2316_ = lean_ctor_get(v_removedVersion_x3f_2315_, 0);
lean_inc(v_val_2316_);
lean_dec_ref_known(v_removedVersion_x3f_2315_, 1);
v___x_2317_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
v___x_2318_ = l_Lean_MessageData_ofName(v___x_2306_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_stringToMessageData(v_val_2316_);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_2293_, v___x_2325_, v___y_2292_, v___y_2287_, v___y_2291_, v___y_2294_, v___y_2288_, v___y_2290_);
lean_dec(v___y_2293_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_dec_ref_known(v___x_2326_, 1);
v___y_2267_ = v___y_2289_;
v___y_2268_ = v___y_2292_;
v___y_2269_ = v___y_2287_;
v___y_2270_ = v___y_2291_;
v___y_2271_ = v___y_2294_;
v___y_2272_ = v___y_2288_;
v___y_2273_ = v___y_2290_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_expType_x3f_2258_);
lean_dec(v_stx_2257_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_dec(v_removedVersion_x3f_2315_);
lean_dec(v___x_2306_);
lean_dec(v___y_2293_);
v___y_2267_ = v___y_2289_;
v___y_2268_ = v___y_2292_;
v___y_2269_ = v___y_2287_;
v___y_2270_ = v___y_2291_;
v___y_2271_ = v___y_2294_;
v___y_2272_ = v___y_2288_;
v___y_2273_ = v___y_2290_;
goto v___jp_2266_;
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_a_2312_);
v___x_2335_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
v___x_2336_ = l_Lean_MessageData_ofName(v___x_2306_);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_2293_, v___x_2339_, v___y_2292_, v___y_2287_, v___y_2291_, v___y_2294_, v___y_2288_, v___y_2290_);
lean_dec(v___y_2293_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_dec_ref_known(v___x_2340_, 1);
v___y_2267_ = v___y_2289_;
v___y_2268_ = v___y_2292_;
v___y_2269_ = v___y_2287_;
v___y_2270_ = v___y_2291_;
v___y_2271_ = v___y_2294_;
v___y_2272_ = v___y_2288_;
v___y_2273_ = v___y_2290_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_expType_x3f_2258_);
lean_dec(v_stx_2257_);
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
}
}
}
}
v___jp_2352_:
{
lean_object* v___x_2361_; uint8_t v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = l_Lean_Syntax_getNumArgs(v_stx_2257_);
v___x_2362_ = lean_nat_dec_eq(v___x_2361_, v_snd_2360_);
v___x_2363_ = 1;
if (v___x_2362_ == 0)
{
lean_dec(v___x_2361_);
lean_inc(v_stx_2257_);
v___y_2287_ = v___y_2353_;
v___y_2288_ = v___y_2354_;
v___y_2289_ = v___x_2363_;
v___y_2290_ = v___y_2357_;
v___y_2291_ = v___y_2356_;
v___y_2292_ = v___y_2355_;
v___y_2293_ = v_fst_2359_;
v___y_2294_ = v___y_2358_;
v___y_2295_ = v_stx_2257_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2364_ = l_Lean_Syntax_getArgs(v_stx_2257_);
v___x_2365_ = lean_unsigned_to_nat(1u);
v___x_2366_ = lean_nat_sub(v___x_2361_, v___x_2365_);
lean_dec(v___x_2361_);
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = l_Array_toSubarray___redArg(v___x_2364_, v___x_2367_, v___x_2366_);
v___x_2369_ = l_Subarray_copy___redArg(v___x_2368_);
lean_inc(v_stx_2257_);
v___x_2370_ = l_Lean_Syntax_setArgs(v_stx_2257_, v___x_2369_);
v___y_2287_ = v___y_2353_;
v___y_2288_ = v___y_2354_;
v___y_2289_ = v___x_2363_;
v___y_2290_ = v___y_2357_;
v___y_2291_ = v___y_2356_;
v___y_2292_ = v___y_2355_;
v___y_2293_ = v_fst_2359_;
v___y_2294_ = v___y_2358_;
v___y_2295_ = v___x_2370_;
goto v___jp_2286_;
}
}
v___jp_2371_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_unsigned_to_nat(2u);
v___x_2379_ = l_Lean_Syntax_getArg(v_stx_2257_, v___x_2378_);
v___x_2380_ = lean_unsigned_to_nat(5u);
v___y_2353_ = v___y_2372_;
v___y_2354_ = v___y_2373_;
v___y_2355_ = v___y_2376_;
v___y_2356_ = v___y_2375_;
v___y_2357_ = v___y_2374_;
v___y_2358_ = v___y_2377_;
v_fst_2359_ = v___x_2379_;
v_snd_2360_ = v___x_2380_;
goto v___jp_2352_;
}
v___jp_2381_:
{
if (v___y_2388_ == 0)
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_stx_2257_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v_stx_2257_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = l_Lean_Syntax_getArg(v_stx_2257_, v___x_2391_);
v___x_2393_ = lean_unsigned_to_nat(4u);
v___y_2353_ = v___y_2382_;
v___y_2354_ = v___y_2383_;
v___y_2355_ = v___y_2386_;
v___y_2356_ = v___y_2385_;
v___y_2357_ = v___y_2384_;
v___y_2358_ = v___y_2387_;
v_fst_2359_ = v___x_2392_;
v_snd_2360_ = v___x_2393_;
goto v___jp_2352_;
}
else
{
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2384_;
v___y_2375_ = v___y_2385_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2387_;
goto v___jp_2371_;
}
}
else
{
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2384_;
v___y_2375_ = v___y_2385_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2387_;
goto v___jp_2371_;
}
}
v___jp_2394_:
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_stx_2257_);
v___x_2402_ = l_Lean_Syntax_isOfKind(v_stx_2257_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_stx_2257_);
v___x_2404_ = l_Lean_Syntax_isOfKind(v_stx_2257_, v___x_2403_);
v___y_2382_ = v___y_2396_;
v___y_2383_ = v___y_2399_;
v___y_2384_ = v___y_2400_;
v___y_2385_ = v___y_2397_;
v___y_2386_ = v___y_2395_;
v___y_2387_ = v___y_2398_;
v___y_2388_ = v___x_2404_;
goto v___jp_2381_;
}
else
{
v___y_2382_ = v___y_2396_;
v___y_2383_ = v___y_2399_;
v___y_2384_ = v___y_2400_;
v___y_2385_ = v___y_2397_;
v___y_2386_ = v___y_2395_;
v___y_2387_ = v___y_2398_;
v___y_2388_ = v___x_2402_;
goto v___jp_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object* v_stx_2442_, lean_object* v_expType_x3f_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(v_stx_2442_, v_expType_x3f_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object* v_00_u03b1_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_2453_, v___y_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2457_, lean_object* v_x_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_2457_, v_x_2458_, v___y_2459_, v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v_x_2458_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object* v_00_u03b1_2462_, lean_object* v_ref_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_2463_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_ref_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_2472_, v_ref_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object* v_00_u03b1_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* v_00_u03b1_2500_, lean_object* v_x_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* v_00_u03b1_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(v_00_u03b1_2510_, v_x_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(lean_object* v_t_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_2520_, v___y_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(lean_object* v_t_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object* v_00_u03b2_2538_, lean_object* v_m_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_2539_, v_a_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object* v_00_u03b2_2542_, lean_object* v_m_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_2542_, v_m_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_m_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object* v_00_u03b1_2546_, lean_object* v_msg_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object* v_00_u03b1_2556_, lean_object* v_msg_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(v_00_u03b1_2556_, v_msg_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object* v_cls_2566_, lean_object* v_msg_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_2566_, v_msg_2567_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object* v_cls_2576_, lean_object* v_msg_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_2576_, v_msg_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object* v_as_2586_, lean_object* v_as_x27_2587_, lean_object* v_b_2588_, lean_object* v_a_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_2587_, v_b_2588_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object* v_as_2598_, lean_object* v_as_x27_2599_, lean_object* v_b_2600_, lean_object* v_a_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_2598_, v_as_x27_2599_, v_b_2600_, v_a_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v_as_x27_2599_);
lean_dec(v_as_2598_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object* v_00_u03b1_2610_, lean_object* v_ref_2611_, lean_object* v_msg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_2611_, v_msg_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_ref_2622_, lean_object* v_msg_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_2621_, v_ref_2622_, v_msg_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v_ref_2622_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(lean_object* v_ref_2632_, lean_object* v_msgData_2633_, uint8_t v_severity_2634_, uint8_t v_isSilent_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2632_, v_msgData_2633_, v_severity_2634_, v_isSilent_2635_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(lean_object* v_ref_2644_, lean_object* v_msgData_2645_, lean_object* v_severity_2646_, lean_object* v_isSilent_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v_severity_boxed_2655_; uint8_t v_isSilent_boxed_2656_; lean_object* v_res_2657_; 
v_severity_boxed_2655_ = lean_unbox(v_severity_2646_);
v_isSilent_boxed_2656_ = lean_unbox(v_isSilent_2647_);
v_res_2657_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_2644_, v_msgData_2645_, v_severity_boxed_2655_, v_isSilent_boxed_2656_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v_ref_2644_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(lean_object* v_00_u03b2_2658_, lean_object* v_a_2659_, lean_object* v_x_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_2659_, v_x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(lean_object* v_00_u03b2_2662_, lean_object* v_a_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_2662_, v_a_2663_, v_x_2664_);
lean_dec(v_x_2664_);
lean_dec(v_a_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object* v_msgData_2666_, lean_object* v_macroStack_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_2666_, v_macroStack_2667_, v___y_2672_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object* v_msgData_2676_, lean_object* v_macroStack_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_2676_, v_macroStack_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2685_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(lean_object* v_00_u03b2_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_2687_, v_x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(lean_object* v_00_u03b2_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_){
_start:
{
uint8_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_2690_, v_x_2691_, v_x_2692_);
lean_dec_ref(v_x_2692_);
lean_dec_ref(v_x_2691_);
v_r_2694_ = lean_box(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(lean_object* v_00_u03b2_2695_, lean_object* v_x_2696_, size_t v_x_2697_, lean_object* v_x_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_2696_, v_x_2697_, v_x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(lean_object* v_00_u03b2_2700_, lean_object* v_x_2701_, lean_object* v_x_2702_, lean_object* v_x_2703_){
_start:
{
size_t v_x_22610__boxed_2704_; uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_x_22610__boxed_2704_ = lean_unbox_usize(v_x_2702_);
lean_dec(v_x_2702_);
v_res_2705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_2700_, v_x_2701_, v_x_22610__boxed_2704_, v_x_2703_);
lean_dec_ref(v_x_2703_);
lean_dec_ref(v_x_2701_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(lean_object* v_00_u03b2_2707_, lean_object* v_keys_2708_, lean_object* v_vals_2709_, lean_object* v_heq_2710_, lean_object* v_i_2711_, lean_object* v_k_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_2708_, v_i_2711_, v_k_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(lean_object* v_00_u03b2_2714_, lean_object* v_keys_2715_, lean_object* v_vals_2716_, lean_object* v_heq_2717_, lean_object* v_i_2718_, lean_object* v_k_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_2714_, v_keys_2715_, v_vals_2716_, v_heq_2717_, v_i_2718_, v_k_2719_);
lean_dec_ref(v_k_2719_);
lean_dec_ref(v_vals_2716_);
lean_dec_ref(v_keys_2715_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2730_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2731_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
v___x_2732_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2733_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2734_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2730_, v___x_2731_, v___x_2732_, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2738_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2739_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2741_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2742_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2738_, v___x_2739_, v___x_2740_, v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2746_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2747_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2749_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2750_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2746_, v___x_2747_, v___x_2748_, v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2754_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2755_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2757_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2758_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2754_, v___x_2755_, v___x_2756_, v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2762_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2763_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
v___x_2764_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2765_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2766_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2762_, v___x_2763_, v___x_2764_, v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2770_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2771_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
v___x_2772_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2773_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2774_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2770_, v___x_2771_, v___x_2772_, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object* v_a_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
return v_res_2776_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___f_2778_; 
v___x_2777_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2778_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2778_, 0, v___x_2777_);
return v___f_2778_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___f_2780_; 
v___x_2779_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2780_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2780_, 0, v___x_2779_);
return v___f_2780_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2(void){
_start:
{
lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; 
v___f_2781_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1);
v___f_2782_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___f_2782_);
lean_ctor_set(v___x_2783_, 1, v___f_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___f_2785_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2);
v___f_2785_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2785_, 0, v___x_2784_);
return v___f_2785_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___f_2787_; 
v___x_2786_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2);
v___f_2787_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2787_, 0, v___x_2786_);
return v___f_2787_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5(void){
_start:
{
lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; 
v___f_2788_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4);
v___f_2789_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___f_2789_);
lean_ctor_set(v___x_2790_, 1, v___f_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___f_2792_; 
v___x_2791_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5);
v___f_2792_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2792_, 0, v___x_2791_);
return v___f_2792_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___f_2794_; 
v___x_2793_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5);
v___f_2794_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2794_, 0, v___x_2793_);
return v___f_2794_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8(void){
_start:
{
lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; 
v___f_2795_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7);
v___f_2796_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___f_2796_);
lean_ctor_set(v___x_2797_, 1, v___f_2795_);
return v___x_2797_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___f_2799_; 
v___x_2798_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8);
v___f_2799_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2799_, 0, v___x_2798_);
return v___f_2799_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___f_2801_; 
v___x_2800_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8);
v___f_2801_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2801_, 0, v___x_2800_);
return v___f_2801_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11(void){
_start:
{
lean_object* v___f_2802_; lean_object* v___f_2803_; lean_object* v___x_2804_; 
v___f_2802_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10);
v___f_2803_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___f_2803_);
lean_ctor_set(v___x_2804_, 1, v___f_2802_);
return v___x_2804_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11);
v___x_2806_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* v_t_2807_, lean_object* v_tp_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2816_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12);
lean_inc_ref(v_tp_2808_);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_tp_2808_);
v___x_2818_ = 1;
v___x_2819_ = lean_box(0);
v___x_2820_ = l_Lean_Elab_Term_elabTermEnsuringType(v_t_2807_, v___x_2817_, v___x_2818_, v___x_2818_, v___x_2819_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; uint8_t v___x_2829_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2829_ = l_Lean_Expr_hasSyntheticSorry(v_a_2821_);
if (v___x_2829_ == 0)
{
v___y_2823_ = v_a_2811_;
v___y_2824_ = v_a_2812_;
v___y_2825_ = v_a_2813_;
v___y_2826_ = v_a_2814_;
goto v___jp_2822_;
}
else
{
lean_object* v___x_227__overap_2830_; lean_object* v___x_2831_; 
v___x_227__overap_2830_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_2816_);
lean_inc(v_a_2814_);
lean_inc_ref(v_a_2813_);
lean_inc(v_a_2812_);
lean_inc_ref(v_a_2811_);
lean_inc(v_a_2810_);
lean_inc_ref(v_a_2809_);
v___x_2831_ = lean_apply_7(v___x_227__overap_2830_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, lean_box(0));
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
v___y_2823_ = v_a_2811_;
v___y_2824_ = v_a_2812_;
v___y_2825_ = v_a_2813_;
v___y_2826_ = v_a_2814_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2821_);
lean_dec_ref(v_tp_2808_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
v___jp_2822_:
{
uint8_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = 1;
v___x_2828_ = l_Lean_Meta_evalExpr___redArg(v_tp_2808_, v_a_2821_, v___x_2827_, v___x_2818_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_tp_2808_);
v_a_2840_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2820_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2820_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object* v_t_2848_, lean_object* v_tp_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2848_, v_tp_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg(){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* v_00_u03b1_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* v_00_u03b1_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2872_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = lean_box(0);
v___x_2874_ = l_Lean_Elab_abortTermExceptionId;
v___x_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* v_00_u03b1_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* v_00_u03b1_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v_00_u03b1_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; lean_object* v_env_2902_; lean_object* v___x_2903_; lean_object* v_mainModule_2904_; lean_object* v___x_2905_; 
v___x_2901_ = lean_st_ref_get(v___y_2899_);
v_env_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc_ref(v_env_2902_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_Environment_header(v_env_2902_);
lean_dec_ref(v_env_2902_);
v_mainModule_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_mainModule_2904_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_mainModule_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_2906_);
lean_dec(v___y_2906_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* v___x_2917_, lean_object* v___x_2918_, uint8_t v___x_2919_, lean_object* v_x_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_inc_ref(v___x_2917_);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2917_);
v___x_2929_ = lean_box(0);
v___x_2930_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2918_, v___x_2928_, v___x_2919_, v___x_2919_, v___x_2929_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; uint8_t v___x_2939_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2939_ = l_Lean_Expr_hasSyntheticSorry(v_a_2931_);
if (v___x_2939_ == 0)
{
v___y_2933_ = v___y_2923_;
v___y_2934_ = v___y_2924_;
v___y_2935_ = v___y_2925_;
v___y_2936_ = v___y_2926_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2940_; lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_a_2931_);
lean_dec_ref(v___x_2917_);
v___x_2940_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
v___jp_2932_:
{
uint8_t v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = 1;
v___x_2938_ = l_Lean_Meta_evalExpr___redArg(v___x_2917_, v_a_2931_, v___x_2937_, v___x_2919_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2938_;
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v___x_2917_);
v_a_2949_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2930_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2930_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
uint8_t v___x_8943__boxed_2968_; lean_object* v_res_2969_; 
v___x_8943__boxed_2968_ = lean_unbox(v___x_2959_);
v_res_2969_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(v___x_2957_, v___x_2958_, v___x_8943__boxed_2968_, v_x_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec_ref(v_x_2960_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(lean_object* v_msgData_2970_, lean_object* v_macroStack_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; lean_object* v_scopes_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_opts_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2974_ = lean_st_ref_get(v___y_2972_);
v_scopes_2975_ = lean_ctor_get(v___x_2974_, 2);
lean_inc(v_scopes_2975_);
lean_dec(v___x_2974_);
v___x_2976_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2977_ = l_List_head_x21___redArg(v___x_2976_, v_scopes_2975_);
lean_dec(v_scopes_2975_);
v_opts_2978_ = lean_ctor_get(v___x_2977_, 1);
lean_inc_ref(v_opts_2978_);
lean_dec(v___x_2977_);
v___x_2979_ = l_Lean_Elab_pp_macroStack;
v___x_2980_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_2978_, v___x_2979_);
lean_dec_ref(v_opts_2978_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; 
lean_dec(v_macroStack_2971_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_msgData_2970_);
return v___x_2981_;
}
else
{
if (lean_obj_tag(v_macroStack_2971_) == 0)
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_msgData_2970_);
return v___x_2982_;
}
else
{
lean_object* v_head_2983_; lean_object* v_after_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2999_; 
v_head_2983_ = lean_ctor_get(v_macroStack_2971_, 0);
lean_inc(v_head_2983_);
v_after_2984_ = lean_ctor_get(v_head_2983_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_head_2983_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v_head_2983_, 0);
lean_dec(v_unused_3000_);
v___x_2986_ = v_head_2983_;
v_isShared_2987_ = v_isSharedCheck_2999_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_after_2984_);
lean_dec(v_head_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2999_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 7);
lean_ctor_set(v___x_2986_, 1, v___x_2988_);
lean_ctor_set(v___x_2986_, 0, v_msgData_2970_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_msgData_2970_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_msgData_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2991_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = l_Lean_MessageData_ofSyntax(v_after_2984_);
v___x_2994_ = l_Lean_indentD(v___x_2993_);
v_msgData_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2995_, 0, v___x_2992_);
lean_ctor_set(v_msgData_2995_, 1, v___x_2994_);
v___x_2996_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_2995_, v_macroStack_2971_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg___boxed(lean_object* v_msgData_3001_, lean_object* v_macroStack_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_msgData_3001_, v_macroStack_3002_, v___y_3003_);
lean_dec(v___y_3003_);
return v_res_3005_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3006_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1);
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
lean_ctor_set(v___x_3011_, 2, v___x_3010_);
lean_ctor_set(v___x_3011_, 3, v___x_3010_);
lean_ctor_set(v___x_3011_, 4, v___x_3009_);
lean_ctor_set(v___x_3011_, 5, v___x_3009_);
lean_ctor_set(v___x_3011_, 6, v___x_3009_);
lean_ctor_set(v___x_3011_, 7, v___x_3009_);
lean_ctor_set(v___x_3011_, 8, v___x_3009_);
lean_ctor_set(v___x_3011_, 9, v___x_3009_);
lean_ctor_set(v___x_3011_, 10, v___x_3009_);
return v___x_3011_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_unsigned_to_nat(32u);
v___x_3013_ = lean_mk_empty_array_with_capacity(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3015_ = ((size_t)5ULL);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_unsigned_to_nat(32u);
v___x_3018_ = lean_mk_empty_array_with_capacity(v___x_3017_);
v___x_3019_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3);
v___x_3020_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3018_);
lean_ctor_set(v___x_3020_, 2, v___x_3016_);
lean_ctor_set(v___x_3020_, 3, v___x_3016_);
lean_ctor_set_usize(v___x_3020_, 4, v___x_3015_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3021_ = lean_box(1);
v___x_3022_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4);
v___x_3023_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1);
v___x_3024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___x_3022_);
lean_ctor_set(v___x_3024_, 2, v___x_3021_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(lean_object* v_msgData_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v_env_3029_; lean_object* v___x_3030_; lean_object* v_scopes_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_opts_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3028_ = lean_st_ref_get(v___y_3026_);
v_env_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc_ref(v_env_3029_);
lean_dec(v___x_3028_);
v___x_3030_ = lean_st_ref_get(v___y_3026_);
v_scopes_3031_ = lean_ctor_get(v___x_3030_, 2);
lean_inc(v_scopes_3031_);
lean_dec(v___x_3030_);
v___x_3032_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3033_ = l_List_head_x21___redArg(v___x_3032_, v_scopes_3031_);
lean_dec(v_scopes_3031_);
v_opts_3034_ = lean_ctor_get(v___x_3033_, 1);
lean_inc_ref(v_opts_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2);
v___x_3036_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__5);
v___x_3037_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3037_, 0, v_env_3029_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
lean_ctor_set(v___x_3037_, 2, v___x_3036_);
lean_ctor_set(v___x_3037_, 3, v_opts_3034_);
v___x_3038_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v_msgData_3025_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___boxed(lean_object* v_msgData_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msgData_3040_, v___y_3041_);
lean_dec(v___y_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(lean_object* v_msg_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Elab_Command_getRef___redArg(v___y_3045_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v_macroStack_3050_; lean_object* v___x_3051_; lean_object* v_a_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v_macroStack_3050_ = lean_ctor_get(v___y_3045_, 4);
v___x_3051_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msg_3044_, v___y_3046_);
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref(v___x_3051_);
v___x_3053_ = l_Lean_Elab_getBetterRef(v_a_3049_, v_macroStack_3050_);
lean_dec(v_a_3049_);
lean_inc(v_macroStack_3050_);
v___x_3054_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_a_3052_, v_macroStack_3050_, v___y_3046_);
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3053_);
lean_ctor_set(v___x_3059_, 1, v_a_3055_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set_tag(v___x_3057_, 1);
lean_ctor_set(v___x_3057_, 0, v___x_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v_msg_3044_);
v_a_3064_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3048_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3048_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg___boxed(lean_object* v_msg_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v_msg_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object* v_ref_3077_, lean_object* v_msg_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Elab_Command_getRef___redArg(v___y_3079_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_fileName_3084_; lean_object* v_fileMap_3085_; lean_object* v_currRecDepth_3086_; lean_object* v_cmdPos_3087_; lean_object* v_macroStack_3088_; lean_object* v_quotContext_x3f_3089_; lean_object* v_currMacroScope_3090_; lean_object* v_snap_x3f_3091_; lean_object* v_cancelTk_x3f_3092_; uint8_t v_suppressElabErrors_3093_; lean_object* v_ref_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v_fileName_3084_ = lean_ctor_get(v___y_3079_, 0);
v_fileMap_3085_ = lean_ctor_get(v___y_3079_, 1);
v_currRecDepth_3086_ = lean_ctor_get(v___y_3079_, 2);
v_cmdPos_3087_ = lean_ctor_get(v___y_3079_, 3);
v_macroStack_3088_ = lean_ctor_get(v___y_3079_, 4);
v_quotContext_x3f_3089_ = lean_ctor_get(v___y_3079_, 5);
v_currMacroScope_3090_ = lean_ctor_get(v___y_3079_, 6);
v_snap_x3f_3091_ = lean_ctor_get(v___y_3079_, 8);
v_cancelTk_x3f_3092_ = lean_ctor_get(v___y_3079_, 9);
v_suppressElabErrors_3093_ = lean_ctor_get_uint8(v___y_3079_, sizeof(void*)*10);
v_ref_3094_ = l_Lean_replaceRef(v_ref_3077_, v_a_3083_);
lean_dec(v_a_3083_);
lean_inc(v_cancelTk_x3f_3092_);
lean_inc(v_snap_x3f_3091_);
lean_inc(v_currMacroScope_3090_);
lean_inc(v_quotContext_x3f_3089_);
lean_inc(v_macroStack_3088_);
lean_inc(v_cmdPos_3087_);
lean_inc(v_currRecDepth_3086_);
lean_inc_ref(v_fileMap_3085_);
lean_inc_ref(v_fileName_3084_);
v___x_3095_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3095_, 0, v_fileName_3084_);
lean_ctor_set(v___x_3095_, 1, v_fileMap_3085_);
lean_ctor_set(v___x_3095_, 2, v_currRecDepth_3086_);
lean_ctor_set(v___x_3095_, 3, v_cmdPos_3087_);
lean_ctor_set(v___x_3095_, 4, v_macroStack_3088_);
lean_ctor_set(v___x_3095_, 5, v_quotContext_x3f_3089_);
lean_ctor_set(v___x_3095_, 6, v_currMacroScope_3090_);
lean_ctor_set(v___x_3095_, 7, v_ref_3094_);
lean_ctor_set(v___x_3095_, 8, v_snap_x3f_3091_);
lean_ctor_set(v___x_3095_, 9, v_cancelTk_x3f_3092_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*10, v_suppressElabErrors_3093_);
v___x_3096_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v_msg_3078_, v___x_3095_, v___y_3080_);
lean_dec_ref_known(v___x_3095_, 10);
return v___x_3096_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_msg_3078_);
v_a_3097_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3082_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3082_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object* v_ref_3105_, lean_object* v_msg_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_ref_3105_, v_msg_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v_ref_3105_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(lean_object* v_cls_3111_, lean_object* v_msg_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Elab_Command_getRef___redArg(v___y_3113_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3167_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msg_3112_, v___y_3114_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3167_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3167_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v_traceState_3124_; lean_object* v_env_3125_; lean_object* v_messages_3126_; lean_object* v_scopes_3127_; lean_object* v_usedQuotCtxts_3128_; lean_object* v_nextMacroScope_3129_; lean_object* v_maxRecDepth_3130_; lean_object* v_ngen_3131_; lean_object* v_auxDeclNGen_3132_; lean_object* v_infoState_3133_; lean_object* v_snapshotTasks_3134_; lean_object* v_prevLinterStates_3135_; lean_object* v_codeQualityEntryTasks_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3166_; 
v___x_3123_ = lean_st_ref_take(v___y_3114_);
v_traceState_3124_ = lean_ctor_get(v___x_3123_, 9);
v_env_3125_ = lean_ctor_get(v___x_3123_, 0);
v_messages_3126_ = lean_ctor_get(v___x_3123_, 1);
v_scopes_3127_ = lean_ctor_get(v___x_3123_, 2);
v_usedQuotCtxts_3128_ = lean_ctor_get(v___x_3123_, 3);
v_nextMacroScope_3129_ = lean_ctor_get(v___x_3123_, 4);
v_maxRecDepth_3130_ = lean_ctor_get(v___x_3123_, 5);
v_ngen_3131_ = lean_ctor_get(v___x_3123_, 6);
v_auxDeclNGen_3132_ = lean_ctor_get(v___x_3123_, 7);
v_infoState_3133_ = lean_ctor_get(v___x_3123_, 8);
v_snapshotTasks_3134_ = lean_ctor_get(v___x_3123_, 10);
v_prevLinterStates_3135_ = lean_ctor_get(v___x_3123_, 11);
v_codeQualityEntryTasks_3136_ = lean_ctor_get(v___x_3123_, 12);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3138_ = v___x_3123_;
v_isShared_3139_ = v_isSharedCheck_3166_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3136_);
lean_inc(v_prevLinterStates_3135_);
lean_inc(v_snapshotTasks_3134_);
lean_inc(v_traceState_3124_);
lean_inc(v_infoState_3133_);
lean_inc(v_auxDeclNGen_3132_);
lean_inc(v_ngen_3131_);
lean_inc(v_maxRecDepth_3130_);
lean_inc(v_nextMacroScope_3129_);
lean_inc(v_usedQuotCtxts_3128_);
lean_inc(v_scopes_3127_);
lean_inc(v_messages_3126_);
lean_inc(v_env_3125_);
lean_dec(v___x_3123_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3166_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
uint64_t v_tid_3140_; lean_object* v_traces_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3165_; 
v_tid_3140_ = lean_ctor_get_uint64(v_traceState_3124_, sizeof(void*)*1);
v_traces_3141_ = lean_ctor_get(v_traceState_3124_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_traceState_3124_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3143_ = v_traceState_3124_;
v_isShared_3144_ = v_isSharedCheck_3165_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_traces_3141_);
lean_dec(v_traceState_3124_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3165_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; double v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3145_ = lean_box(0);
v___x_3146_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_3147_ = 0;
v___x_3148_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3149_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3149_, 0, v_cls_3111_);
lean_ctor_set(v___x_3149_, 1, v___x_3145_);
lean_ctor_set(v___x_3149_, 2, v___x_3148_);
lean_ctor_set_float(v___x_3149_, sizeof(void*)*3, v___x_3146_);
lean_ctor_set_float(v___x_3149_, sizeof(void*)*3 + 8, v___x_3146_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*3 + 16, v___x_3147_);
v___x_3150_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_3151_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3149_);
lean_ctor_set(v___x_3151_, 1, v_a_3119_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_a_3117_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_PersistentArray_push___redArg(v_traces_3141_, v___x_3152_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v___x_3153_);
v___x_3155_ = v___x_3143_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3153_);
lean_ctor_set_uint64(v_reuseFailAlloc_3164_, sizeof(void*)*1, v_tid_3140_);
v___x_3155_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 9, v___x_3155_);
v___x_3157_ = v___x_3138_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_env_3125_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_messages_3126_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_scopes_3127_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v_usedQuotCtxts_3128_);
lean_ctor_set(v_reuseFailAlloc_3163_, 4, v_nextMacroScope_3129_);
lean_ctor_set(v_reuseFailAlloc_3163_, 5, v_maxRecDepth_3130_);
lean_ctor_set(v_reuseFailAlloc_3163_, 6, v_ngen_3131_);
lean_ctor_set(v_reuseFailAlloc_3163_, 7, v_auxDeclNGen_3132_);
lean_ctor_set(v_reuseFailAlloc_3163_, 8, v_infoState_3133_);
lean_ctor_set(v_reuseFailAlloc_3163_, 9, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3163_, 10, v_snapshotTasks_3134_);
lean_ctor_set(v_reuseFailAlloc_3163_, 11, v_prevLinterStates_3135_);
lean_ctor_set(v_reuseFailAlloc_3163_, 12, v_codeQualityEntryTasks_3136_);
v___x_3157_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3158_ = lean_st_ref_put(v___y_3114_, v___x_3157_);
v___x_3159_ = lean_box(0);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3159_);
v___x_3161_ = v___x_3121_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v_msg_3112_);
lean_dec(v_cls_3111_);
v_a_3168_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3116_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3116_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4___boxed(lean_object* v_cls_3176_, lean_object* v_msg_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_3176_, v_msg_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(lean_object* v_mod_3182_, uint8_t v_isMeta_3183_, lean_object* v_hint_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; lean_object* v_env_3189_; uint8_t v_isExporting_3190_; lean_object* v___x_3191_; lean_object* v_env_3192_; lean_object* v___x_3193_; lean_object* v_entry_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___y_3199_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3188_ = lean_st_ref_get(v___y_3186_);
v_env_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc_ref(v_env_3189_);
lean_dec(v___x_3188_);
v_isExporting_3190_ = lean_ctor_get_uint8(v_env_3189_, sizeof(void*)*8);
lean_dec_ref(v_env_3189_);
v___x_3191_ = lean_st_ref_get(v___y_3186_);
v_env_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc_ref(v_env_3192_);
lean_dec(v___x_3191_);
v___x_3193_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_3182_);
v_entry_3194_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3194_, 0, v_mod_3182_);
lean_ctor_set_uint8(v_entry_3194_, sizeof(void*)*1, v_isExporting_3190_);
lean_ctor_set_uint8(v_entry_3194_, sizeof(void*)*1 + 1, v_isMeta_3183_);
v___x_3195_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3196_ = lean_box(1);
v___x_3197_ = lean_box(0);
v___x_3227_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3193_, v___x_3195_, v_env_3192_, v___x_3196_, v___x_3197_);
v___x_3228_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_3227_, v_entry_3194_);
lean_dec(v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_scopes_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_opts_3235_; uint8_t v_hasTrace_3236_; 
v___x_3229_ = l_Lean_inheritedTraceOptions;
v___x_3230_ = lean_st_ref_get(v___x_3229_);
v___x_3231_ = lean_st_ref_get(v___y_3186_);
v_scopes_3232_ = lean_ctor_get(v___x_3231_, 2);
lean_inc(v_scopes_3232_);
lean_dec(v___x_3231_);
v___x_3233_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3234_ = l_List_head_x21___redArg(v___x_3233_, v_scopes_3232_);
lean_dec(v_scopes_3232_);
v_opts_3235_ = lean_ctor_get(v___x_3234_, 1);
lean_inc_ref(v_opts_3235_);
lean_dec(v___x_3234_);
v_hasTrace_3236_ = lean_ctor_get_uint8(v_opts_3235_, sizeof(void*)*1);
if (v_hasTrace_3236_ == 0)
{
lean_dec_ref(v_opts_3235_);
lean_dec(v___x_3230_);
lean_dec(v_hint_3184_);
lean_dec(v_mod_3182_);
v___y_3199_ = v___y_3186_;
goto v___jp_3198_;
}
else
{
lean_object* v_cls_3237_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_cls_3237_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_3257_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3230_, v_opts_3235_, v___x_3257_);
lean_dec_ref(v_opts_3235_);
lean_dec(v___x_3230_);
if (v___x_3258_ == 0)
{
lean_dec(v_hint_3184_);
lean_dec(v_mod_3182_);
v___y_3199_ = v___y_3186_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3259_; lean_object* v___y_3261_; 
v___x_3259_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_3190_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21));
v___y_3261_ = v___x_3268_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22));
v___y_3261_ = v___x_3269_;
goto v___jp_3260_;
}
v___jp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_inc_ref(v___y_3261_);
v___x_3262_ = l_Lean_stringToMessageData(v___y_3261_);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3259_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
if (v_isMeta_3183_ == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_3244_ = v___x_3265_;
v___y_3245_ = v___x_3266_;
goto v___jp_3243_;
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_3244_ = v___x_3265_;
v___y_3245_ = v___x_3267_;
goto v___jp_3243_;
}
}
}
v___jp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___y_3239_);
lean_ctor_set(v___x_3241_, 1, v___y_3240_);
v___x_3242_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_3237_, v___x_3241_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_dec_ref_known(v___x_3242_, 1);
v___y_3199_ = v___y_3186_;
goto v___jp_3198_;
}
else
{
lean_dec_ref_known(v_entry_3194_, 1);
return v___x_3242_;
}
}
v___jp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
lean_inc_ref(v___y_3245_);
v___x_3246_ = l_Lean_stringToMessageData(v___y_3245_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___y_3244_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_MessageData_ofName(v_mod_3182_);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_Name_isAnonymous(v_hint_3184_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_3254_ = l_Lean_MessageData_ofName(v_hint_3184_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___y_3239_ = v___x_3251_;
v___y_3240_ = v___x_3255_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3256_; 
lean_dec(v_hint_3184_);
v___x_3256_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
v___y_3239_ = v___x_3251_;
v___y_3240_ = v___x_3256_;
goto v___jp_3238_;
}
}
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec_ref_known(v_entry_3194_, 1);
lean_dec(v_hint_3184_);
lean_dec(v_mod_3182_);
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
return v___x_3271_;
}
v___jp_3198_:
{
lean_object* v___x_3200_; lean_object* v_toEnvExtension_3201_; lean_object* v_env_3202_; lean_object* v_messages_3203_; lean_object* v_scopes_3204_; lean_object* v_usedQuotCtxts_3205_; lean_object* v_nextMacroScope_3206_; lean_object* v_maxRecDepth_3207_; lean_object* v_ngen_3208_; lean_object* v_auxDeclNGen_3209_; lean_object* v_infoState_3210_; lean_object* v_traceState_3211_; lean_object* v_snapshotTasks_3212_; lean_object* v_prevLinterStates_3213_; lean_object* v_codeQualityEntryTasks_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3226_; 
v___x_3200_ = lean_st_ref_take(v___y_3199_);
v_toEnvExtension_3201_ = lean_ctor_get(v___x_3195_, 0);
v_env_3202_ = lean_ctor_get(v___x_3200_, 0);
v_messages_3203_ = lean_ctor_get(v___x_3200_, 1);
v_scopes_3204_ = lean_ctor_get(v___x_3200_, 2);
v_usedQuotCtxts_3205_ = lean_ctor_get(v___x_3200_, 3);
v_nextMacroScope_3206_ = lean_ctor_get(v___x_3200_, 4);
v_maxRecDepth_3207_ = lean_ctor_get(v___x_3200_, 5);
v_ngen_3208_ = lean_ctor_get(v___x_3200_, 6);
v_auxDeclNGen_3209_ = lean_ctor_get(v___x_3200_, 7);
v_infoState_3210_ = lean_ctor_get(v___x_3200_, 8);
v_traceState_3211_ = lean_ctor_get(v___x_3200_, 9);
v_snapshotTasks_3212_ = lean_ctor_get(v___x_3200_, 10);
v_prevLinterStates_3213_ = lean_ctor_get(v___x_3200_, 11);
v_codeQualityEntryTasks_3214_ = lean_ctor_get(v___x_3200_, 12);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3216_ = v___x_3200_;
v_isShared_3217_ = v_isSharedCheck_3226_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3214_);
lean_inc(v_prevLinterStates_3213_);
lean_inc(v_snapshotTasks_3212_);
lean_inc(v_traceState_3211_);
lean_inc(v_infoState_3210_);
lean_inc(v_auxDeclNGen_3209_);
lean_inc(v_ngen_3208_);
lean_inc(v_maxRecDepth_3207_);
lean_inc(v_nextMacroScope_3206_);
lean_inc(v_usedQuotCtxts_3205_);
lean_inc(v_scopes_3204_);
lean_inc(v_messages_3203_);
lean_inc(v_env_3202_);
lean_dec(v___x_3200_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3226_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v_asyncMode_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
v_asyncMode_3218_ = lean_ctor_get(v_toEnvExtension_3201_, 2);
v___x_3219_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3195_, v_env_3202_, v_entry_3194_, v_asyncMode_3218_, v___x_3197_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3219_);
v___x_3221_ = v___x_3216_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_messages_3203_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_scopes_3204_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_usedQuotCtxts_3205_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_nextMacroScope_3206_);
lean_ctor_set(v_reuseFailAlloc_3225_, 5, v_maxRecDepth_3207_);
lean_ctor_set(v_reuseFailAlloc_3225_, 6, v_ngen_3208_);
lean_ctor_set(v_reuseFailAlloc_3225_, 7, v_auxDeclNGen_3209_);
lean_ctor_set(v_reuseFailAlloc_3225_, 8, v_infoState_3210_);
lean_ctor_set(v_reuseFailAlloc_3225_, 9, v_traceState_3211_);
lean_ctor_set(v_reuseFailAlloc_3225_, 10, v_snapshotTasks_3212_);
lean_ctor_set(v_reuseFailAlloc_3225_, 11, v_prevLinterStates_3213_);
lean_ctor_set(v_reuseFailAlloc_3225_, 12, v_codeQualityEntryTasks_3214_);
v___x_3221_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = lean_st_ref_put(v___y_3199_, v___x_3221_);
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(lean_object* v_mod_3272_, lean_object* v_isMeta_3273_, lean_object* v_hint_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
uint8_t v_isMeta_boxed_3278_; lean_object* v_res_3279_; 
v_isMeta_boxed_3278_ = lean_unbox(v_isMeta_3273_);
v_res_3279_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_3272_, v_isMeta_boxed_3278_, v_hint_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(lean_object* v___x_3280_, lean_object* v_declName_3281_, lean_object* v_as_3282_, size_t v_sz_3283_, size_t v_i_3284_, lean_object* v_b_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_usize_dec_lt(v_i_3284_, v_sz_3283_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
lean_dec(v_declName_3281_);
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_b_3285_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; lean_object* v_modules_3292_; lean_object* v___x_3293_; lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v_toImport_3296_; lean_object* v_module_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3291_ = l_Lean_Environment_header(v___x_3280_);
v_modules_3292_ = lean_ctor_get(v___x_3291_, 3);
lean_inc_ref(v_modules_3292_);
lean_dec_ref(v___x_3291_);
v___x_3293_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3294_ = lean_array_uget_borrowed(v_as_3282_, v_i_3284_);
v___x_3295_ = lean_array_get(v___x_3293_, v_modules_3292_, v_a_3294_);
lean_dec_ref(v_modules_3292_);
v_toImport_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_ref(v_toImport_3296_);
lean_dec(v___x_3295_);
v_module_3297_ = lean_ctor_get(v_toImport_3296_, 0);
lean_inc(v_module_3297_);
lean_dec_ref(v_toImport_3296_);
v___x_3298_ = 0;
lean_inc(v_declName_3281_);
v___x_3299_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3297_, v___x_3298_, v_declName_3281_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; 
lean_dec_ref_known(v___x_3299_, 1);
v___x_3300_ = lean_box(0);
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3284_, v___x_3301_);
v_i_3284_ = v___x_3302_;
v_b_3285_ = v___x_3300_;
goto _start;
}
else
{
lean_dec(v_declName_3281_);
return v___x_3299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(lean_object* v___x_3304_, lean_object* v_declName_3305_, lean_object* v_as_3306_, lean_object* v_sz_3307_, lean_object* v_i_3308_, lean_object* v_b_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
size_t v_sz_boxed_3313_; size_t v_i_boxed_3314_; lean_object* v_res_3315_; 
v_sz_boxed_3313_ = lean_unbox_usize(v_sz_3307_);
lean_dec(v_sz_3307_);
v_i_boxed_3314_ = lean_unbox_usize(v_i_3308_);
lean_dec(v_i_3308_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_3304_, v_declName_3305_, v_as_3306_, v_sz_boxed_3313_, v_i_boxed_3314_, v_b_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec_ref(v_as_3306_);
lean_dec_ref(v___x_3304_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(lean_object* v_declName_3316_, uint8_t v_isMeta_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v_env_3325_; lean_object* v___y_3327_; lean_object* v___x_3340_; 
v___x_3321_ = lean_st_ref_get(v___y_3319_);
v_env_3325_ = lean_ctor_get(v___x_3321_, 0);
lean_inc_ref(v_env_3325_);
lean_dec(v___x_3321_);
v___x_3340_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3325_, v_declName_3316_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_dec_ref(v_env_3325_);
lean_dec(v_declName_3316_);
goto v___jp_3322_;
}
else
{
lean_object* v_val_3341_; lean_object* v___x_3342_; lean_object* v_modules_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_val_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_val_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = l_Lean_Environment_header(v_env_3325_);
v_modules_3343_ = lean_ctor_get(v___x_3342_, 3);
lean_inc_ref(v_modules_3343_);
lean_dec_ref(v___x_3342_);
v___x_3344_ = lean_array_get_size(v_modules_3343_);
v___x_3345_ = lean_nat_dec_lt(v_val_3341_, v___x_3344_);
if (v___x_3345_ == 0)
{
lean_dec_ref(v_modules_3343_);
lean_dec(v_val_3341_);
lean_dec_ref(v_env_3325_);
lean_dec(v_declName_3316_);
goto v___jp_3322_;
}
else
{
lean_object* v___x_3346_; lean_object* v_env_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___y_3351_; 
v___x_3346_ = lean_st_ref_get(v___y_3319_);
v_env_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_ref(v_env_3347_);
lean_dec(v___x_3346_);
v___x_3348_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
v___x_3349_ = lean_array_fget(v_modules_3343_, v_val_3341_);
lean_dec(v_val_3341_);
lean_dec_ref(v_modules_3343_);
if (v_isMeta_3317_ == 0)
{
lean_dec_ref(v_env_3347_);
v___y_3351_ = v_isMeta_3317_;
goto v___jp_3350_;
}
else
{
uint8_t v___x_3362_; 
lean_inc(v_declName_3316_);
v___x_3362_ = l_Lean_isMarkedMeta(v_env_3347_, v_declName_3316_);
if (v___x_3362_ == 0)
{
v___y_3351_ = v_isMeta_3317_;
goto v___jp_3350_;
}
else
{
uint8_t v___x_3363_; 
v___x_3363_ = 0;
v___y_3351_ = v___x_3363_;
goto v___jp_3350_;
}
}
v___jp_3350_:
{
lean_object* v_toImport_3352_; lean_object* v_module_3353_; lean_object* v___x_3354_; 
v_toImport_3352_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_ref(v_toImport_3352_);
lean_dec(v___x_3349_);
v_module_3353_ = lean_ctor_get(v_toImport_3352_, 0);
lean_inc(v_module_3353_);
lean_dec_ref(v_toImport_3352_);
lean_inc(v_declName_3316_);
v___x_3354_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3353_, v___y_3351_, v_declName_3316_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_dec_ref_known(v___x_3354_, 1);
v___x_3355_ = l_Lean_indirectModUseExt;
v___x_3356_ = lean_box(1);
v___x_3357_ = lean_box(0);
lean_inc_ref(v_env_3325_);
v___x_3358_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3348_, v___x_3355_, v_env_3325_, v___x_3356_, v___x_3357_);
v___x_3359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_3358_, v_declName_3316_);
lean_dec(v___x_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3360_; 
v___x_3360_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3));
v___y_3327_ = v___x_3360_;
goto v___jp_3326_;
}
else
{
lean_object* v_val_3361_; 
v_val_3361_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v___x_3359_, 1);
v___y_3327_ = v_val_3361_;
goto v___jp_3326_;
}
}
else
{
lean_dec_ref(v_env_3325_);
lean_dec(v_declName_3316_);
return v___x_3354_;
}
}
}
}
v___jp_3322_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
v___jp_3326_:
{
lean_object* v___x_3328_; size_t v_sz_3329_; size_t v___x_3330_; lean_object* v___x_3331_; 
v___x_3328_ = lean_box(0);
v_sz_3329_ = lean_array_size(v___y_3327_);
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_3325_, v_declName_3316_, v___y_3327_, v_sz_3329_, v___x_3330_, v___x_3328_, v___y_3318_, v___y_3319_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v_env_3325_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v___x_3331_, 0);
lean_dec(v_unused_3339_);
v___x_3333_ = v___x_3331_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_dec(v___x_3331_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3328_);
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3328_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
else
{
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(lean_object* v_declName_3364_, lean_object* v_isMeta_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
uint8_t v_isMeta_boxed_3369_; lean_object* v_res_3370_; 
v_isMeta_boxed_3369_ = lean_unbox(v_isMeta_3365_);
v_res_3370_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_3364_, v_isMeta_boxed_3369_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3370_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3));
v___x_3380_ = l_Lean_stringToMessageData(v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11);
v___x_3393_ = l_Lean_MessageData_note(v___x_3392_);
return v___x_3393_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17(void){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = lean_box(0);
v___x_3403_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3404_ = l_Lean_mkConst(v___x_3403_, v___x_3402_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* v_x_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3466_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
lean_inc(v_x_3411_);
v___x_3467_ = l_Lean_Syntax_isOfKind(v_x_3411_, v___x_3466_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; 
lean_dec(v_x_3411_);
v___x_3468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3468_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = l_Lean_Syntax_getArg(v_x_3411_, v___x_3469_);
v___x_3471_ = lean_unsigned_to_nat(1u);
v___x_3472_ = l_Lean_Syntax_matchesNull(v___x_3470_, v___x_3471_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
lean_dec(v_x_3411_);
v___x_3473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v_id_3475_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; uint8_t v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3474_ = lean_unsigned_to_nat(2u);
v_id_3475_ = l_Lean_Syntax_getArg(v_x_3411_, v___x_3474_);
v___x_3495_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
lean_inc(v_id_3475_);
v___x_3496_ = l_Lean_Syntax_isOfKind(v_id_3475_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v_id_3475_);
lean_dec(v_x_3411_);
v___x_3497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Elab_Command_getRef___redArg(v_a_3412_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; lean_object* v_fileName_3501_; lean_object* v_fileMap_3502_; lean_object* v_currRecDepth_3503_; lean_object* v_cmdPos_3504_; lean_object* v_macroStack_3505_; lean_object* v_quotContext_x3f_3506_; lean_object* v_currMacroScope_3507_; lean_object* v_snap_x3f_3508_; lean_object* v_cancelTk_x3f_3509_; uint8_t v_suppressElabErrors_3510_; lean_object* v_env_3511_; lean_object* v___x_3512_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v_cmd_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v_ref_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = lean_st_ref_get(v_a_3413_);
v_fileName_3501_ = lean_ctor_get(v_a_3412_, 0);
v_fileMap_3502_ = lean_ctor_get(v_a_3412_, 1);
v_currRecDepth_3503_ = lean_ctor_get(v_a_3412_, 2);
v_cmdPos_3504_ = lean_ctor_get(v_a_3412_, 3);
v_macroStack_3505_ = lean_ctor_get(v_a_3412_, 4);
v_quotContext_x3f_3506_ = lean_ctor_get(v_a_3412_, 5);
v_currMacroScope_3507_ = lean_ctor_get(v_a_3412_, 6);
v_snap_x3f_3508_ = lean_ctor_get(v_a_3412_, 8);
v_cancelTk_x3f_3509_ = lean_ctor_get(v_a_3412_, 9);
v_suppressElabErrors_3510_ = lean_ctor_get_uint8(v_a_3412_, sizeof(void*)*10);
v_env_3511_ = lean_ctor_get(v___x_3500_, 0);
lean_inc_ref(v_env_3511_);
lean_dec(v___x_3500_);
v___x_3512_ = lean_box(1);
v_cmd_3559_ = l_Lean_Syntax_getArg(v_x_3411_, v___x_3471_);
v___x_3560_ = lean_unsigned_to_nat(3u);
v___x_3561_ = l_Lean_Syntax_getArg(v_x_3411_, v___x_3560_);
lean_dec(v_x_3411_);
v_ref_3588_ = l_Lean_replaceRef(v_cmd_3559_, v_a_3499_);
lean_dec(v_a_3499_);
lean_dec(v_cmd_3559_);
lean_inc(v_cancelTk_x3f_3509_);
lean_inc(v_snap_x3f_3508_);
lean_inc(v_currMacroScope_3507_);
lean_inc(v_quotContext_x3f_3506_);
lean_inc(v_macroStack_3505_);
lean_inc(v_cmdPos_3504_);
lean_inc(v_currRecDepth_3503_);
lean_inc_ref(v_fileMap_3502_);
lean_inc_ref(v_fileName_3501_);
v___x_3589_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3589_, 0, v_fileName_3501_);
lean_ctor_set(v___x_3589_, 1, v_fileMap_3502_);
lean_ctor_set(v___x_3589_, 2, v_currRecDepth_3503_);
lean_ctor_set(v___x_3589_, 3, v_cmdPos_3504_);
lean_ctor_set(v___x_3589_, 4, v_macroStack_3505_);
lean_ctor_set(v___x_3589_, 5, v_quotContext_x3f_3506_);
lean_ctor_set(v___x_3589_, 6, v_currMacroScope_3507_);
lean_ctor_set(v___x_3589_, 7, v_ref_3588_);
lean_ctor_set(v___x_3589_, 8, v_snap_x3f_3508_);
lean_ctor_set(v___x_3589_, 9, v_cancelTk_x3f_3509_);
lean_ctor_set_uint8(v___x_3589_, sizeof(void*)*10, v_suppressElabErrors_3510_);
v___x_3590_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3591_ = l_Lean_Environment_contains(v_env_3511_, v___x_3590_, v___x_3496_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec(v___x_3561_);
lean_dec(v_id_3475_);
v___x_3592_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
v___x_3593_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v___x_3592_, v___x_3589_, v_a_3413_);
lean_dec_ref_known(v___x_3589_, 10);
return v___x_3593_;
}
else
{
v___y_3563_ = v___x_3589_;
v___y_3564_ = v_a_3413_;
goto v___jp_3562_;
}
v___jp_3513_:
{
lean_object* v___x_3518_; lean_object* v_env_3519_; lean_object* v___x_3520_; lean_object* v_toEnvExtension_3521_; lean_object* v_asyncMode_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3518_ = lean_st_ref_get(v___y_3517_);
v_env_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc_ref(v_env_3519_);
lean_dec(v___x_3518_);
v___x_3520_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3521_ = lean_ctor_get(v___x_3520_, 0);
v_asyncMode_3522_ = lean_ctor_get(v_toEnvExtension_3521_, 2);
v___x_3523_ = lean_box(0);
v___x_3524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3512_, v___x_3520_, v_env_3519_, v_asyncMode_3522_, v___x_3523_);
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_3515_, v___x_3524_);
lean_dec(v___x_3524_);
if (v___x_3525_ == 0)
{
v___y_3487_ = v___y_3514_;
v___y_3488_ = v___y_3515_;
v___y_3489_ = v___y_3516_;
v___y_3490_ = v___y_3517_;
goto v___jp_3486_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v___y_3514_);
v___x_3526_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
v___x_3527_ = l_Lean_MessageData_ofName(v___y_3515_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3530_, v___y_3516_, v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v_id_3475_);
return v___x_3531_;
}
}
v___jp_3532_:
{
lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = l_Lean_Name_getNumParts(v___y_3534_);
v___x_3538_ = lean_nat_dec_eq(v___x_3537_, v___x_3474_);
lean_dec(v___x_3537_);
if (v___x_3538_ == 0)
{
if (v___x_3472_ == 0)
{
v___y_3514_ = v___y_3533_;
v___y_3515_ = v___y_3534_;
v___y_3516_ = v___y_3535_;
v___y_3517_ = v___y_3536_;
goto v___jp_3513_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref(v___y_3533_);
v___x_3539_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
v___x_3540_ = l_Lean_MessageData_ofName(v___y_3534_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
v___x_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3543_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3545_, v___y_3535_, v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v_id_3475_);
return v___x_3546_;
}
}
else
{
v___y_3514_ = v___y_3533_;
v___y_3515_ = v___y_3534_;
v___y_3516_ = v___y_3535_;
v___y_3517_ = v___y_3536_;
goto v___jp_3513_;
}
}
v___jp_3547_:
{
uint8_t v___x_3552_; 
v___x_3552_ = l_Lean_Name_hasMacroScopes(v___y_3549_);
if (v___x_3552_ == 0)
{
v___y_3533_ = v___y_3548_;
v___y_3534_ = v___y_3549_;
v___y_3535_ = v___y_3550_;
v___y_3536_ = v___y_3551_;
goto v___jp_3532_;
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
v___x_3553_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
lean_inc(v_id_3475_);
v___x_3554_ = l_Lean_MessageData_ofSyntax(v_id_3475_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3557_, v___y_3550_, v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v_id_3475_);
return v___x_3558_;
}
}
v___jp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3566_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_3565_, v___x_3496_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; 
lean_dec_ref_known(v___x_3566_, 1);
v___x_3567_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
v___x_3568_ = lean_box(v___x_3496_);
v___f_3569_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3569_, 0, v___x_3567_);
lean_closure_set(v___f_3569_, 1, v___x_3561_);
lean_closure_set(v___f_3569_, 2, v___x_3568_);
v___x_3570_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3569_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v___x_3572_ = l_Lean_TSyntax_getId(v_id_3475_);
v___x_3573_ = l_Lean_Name_isAnonymous(v___x_3572_);
if (v___x_3573_ == 0)
{
v___y_3548_ = v_a_3571_;
v___y_3549_ = v___x_3572_;
v___y_3550_ = v___y_3563_;
v___y_3551_ = v___y_3564_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec(v___x_3572_);
lean_dec(v_a_3571_);
v___x_3574_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
lean_inc(v_id_3475_);
v___x_3575_ = l_Lean_MessageData_ofSyntax(v_id_3475_);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3578_, v___y_3563_, v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v_id_3475_);
return v___x_3579_;
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v___y_3563_);
lean_dec(v_id_3475_);
v_a_3580_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3570_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3570_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_dec_ref(v___y_3563_);
lean_dec(v___x_3561_);
lean_dec(v_id_3475_);
return v___x_3566_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_id_3475_);
lean_dec(v_x_3411_);
v_a_3594_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3498_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3498_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
v___jp_3476_:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Syntax_getTailPos_x3f(v_id_3475_, v___y_3481_);
lean_dec(v_id_3475_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_inc(v___y_3483_);
v___y_3416_ = v___y_3477_;
v___y_3417_ = v___y_3478_;
v___y_3418_ = v___y_3479_;
v___y_3419_ = v___y_3480_;
v___y_3420_ = v___y_3482_;
v___y_3421_ = v___y_3483_;
v___y_3422_ = v___y_3483_;
goto v___jp_3415_;
}
else
{
lean_object* v_val_3485_; 
v_val_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_val_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___y_3416_ = v___y_3477_;
v___y_3417_ = v___y_3478_;
v___y_3418_ = v___y_3479_;
v___y_3419_ = v___y_3480_;
v___y_3420_ = v___y_3482_;
v___y_3421_ = v___y_3483_;
v___y_3422_ = v_val_3485_;
goto v___jp_3415_;
}
}
v___jp_3486_:
{
lean_object* v_fileMap_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; 
v_fileMap_3491_ = lean_ctor_get(v___y_3489_, 1);
lean_inc_ref(v_fileMap_3491_);
v___x_3492_ = 0;
v___x_3493_ = l_Lean_Syntax_getPos_x3f(v_id_3475_, v___x_3492_);
if (lean_obj_tag(v___x_3493_) == 0)
{
v___y_3477_ = v___y_3490_;
v___y_3478_ = v___y_3487_;
v___y_3479_ = v___y_3489_;
v___y_3480_ = v_fileMap_3491_;
v___y_3481_ = v___x_3492_;
v___y_3482_ = v___y_3488_;
v___y_3483_ = v___x_3469_;
goto v___jp_3476_;
}
else
{
lean_object* v_val_3494_; 
v_val_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_val_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___y_3477_ = v___y_3490_;
v___y_3478_ = v___y_3487_;
v___y_3479_ = v___y_3489_;
v___y_3480_ = v_fileMap_3491_;
v___y_3481_ = v___x_3492_;
v___y_3482_ = v___y_3488_;
v___y_3483_ = v_val_3494_;
goto v___jp_3476_;
}
}
}
}
v___jp_3415_:
{
lean_object* v___x_3423_; lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v___y_3418_);
v___x_3423_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_3416_);
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3465_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3465_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v_env_3429_; lean_object* v_messages_3430_; lean_object* v_scopes_3431_; lean_object* v_usedQuotCtxts_3432_; lean_object* v_nextMacroScope_3433_; lean_object* v_maxRecDepth_3434_; lean_object* v_ngen_3435_; lean_object* v_auxDeclNGen_3436_; lean_object* v_infoState_3437_; lean_object* v_traceState_3438_; lean_object* v_snapshotTasks_3439_; lean_object* v_prevLinterStates_3440_; lean_object* v_codeQualityEntryTasks_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3464_; 
v___x_3428_ = lean_st_ref_take(v___y_3416_);
v_env_3429_ = lean_ctor_get(v___x_3428_, 0);
v_messages_3430_ = lean_ctor_get(v___x_3428_, 1);
v_scopes_3431_ = lean_ctor_get(v___x_3428_, 2);
v_usedQuotCtxts_3432_ = lean_ctor_get(v___x_3428_, 3);
v_nextMacroScope_3433_ = lean_ctor_get(v___x_3428_, 4);
v_maxRecDepth_3434_ = lean_ctor_get(v___x_3428_, 5);
v_ngen_3435_ = lean_ctor_get(v___x_3428_, 6);
v_auxDeclNGen_3436_ = lean_ctor_get(v___x_3428_, 7);
v_infoState_3437_ = lean_ctor_get(v___x_3428_, 8);
v_traceState_3438_ = lean_ctor_get(v___x_3428_, 9);
v_snapshotTasks_3439_ = lean_ctor_get(v___x_3428_, 10);
v_prevLinterStates_3440_ = lean_ctor_get(v___x_3428_, 11);
v_codeQualityEntryTasks_3441_ = lean_ctor_get(v___x_3428_, 12);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3443_ = v___x_3428_;
v_isShared_3444_ = v_isSharedCheck_3464_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3441_);
lean_inc(v_prevLinterStates_3440_);
lean_inc(v_snapshotTasks_3439_);
lean_inc(v_traceState_3438_);
lean_inc(v_infoState_3437_);
lean_inc(v_auxDeclNGen_3436_);
lean_inc(v_ngen_3435_);
lean_inc(v_maxRecDepth_3434_);
lean_inc(v_nextMacroScope_3433_);
lean_inc(v_usedQuotCtxts_3432_);
lean_inc(v_scopes_3431_);
lean_inc(v_messages_3430_);
lean_inc(v_env_3429_);
lean_dec(v___x_3428_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3464_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v_toEnvExtension_3446_; lean_object* v_asyncMode_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3445_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3446_ = lean_ctor_get(v___x_3445_, 0);
v_asyncMode_3447_ = lean_ctor_get(v_toEnvExtension_3446_, 2);
v___x_3448_ = l_Lean_DeclarationRange_ofStringPositions(v___y_3419_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec(v___y_3421_);
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3424_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
v___x_3451_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v___y_3417_);
lean_ctor_set(v___x_3452_, 2, v___x_3450_);
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___y_3420_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = lean_box(0);
v___x_3455_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3445_, v_env_3429_, v___x_3453_, v_asyncMode_3447_, v___x_3454_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3455_);
v___x_3457_ = v___x_3443_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_messages_3430_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_scopes_3431_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_usedQuotCtxts_3432_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_nextMacroScope_3433_);
lean_ctor_set(v_reuseFailAlloc_3463_, 5, v_maxRecDepth_3434_);
lean_ctor_set(v_reuseFailAlloc_3463_, 6, v_ngen_3435_);
lean_ctor_set(v_reuseFailAlloc_3463_, 7, v_auxDeclNGen_3436_);
lean_ctor_set(v_reuseFailAlloc_3463_, 8, v_infoState_3437_);
lean_ctor_set(v_reuseFailAlloc_3463_, 9, v_traceState_3438_);
lean_ctor_set(v_reuseFailAlloc_3463_, 10, v_snapshotTasks_3439_);
lean_ctor_set(v_reuseFailAlloc_3463_, 11, v_prevLinterStates_3440_);
lean_ctor_set(v_reuseFailAlloc_3463_, 12, v_codeQualityEntryTasks_3441_);
v___x_3457_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3458_ = lean_st_ref_put(v___y_3416_, v___x_3457_);
v___x_3459_ = lean_box(0);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3459_);
v___x_3461_ = v___x_3426_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object* v_x_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object* v_00_u03b1_3607_, lean_object* v_ref_3608_, lean_object* v_msg_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_ref_3608_, v_msg_3609_, v___y_3610_, v___y_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object* v_00_u03b1_3614_, lean_object* v_ref_3615_, lean_object* v_msg_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(v_00_u03b1_3614_, v_ref_3615_, v_msg_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v_ref_3615_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7(lean_object* v_msgData_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msgData_3621_, v___y_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___boxed(lean_object* v_msgData_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7(v_msgData_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5(lean_object* v_00_u03b1_3631_, lean_object* v_msg_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v_msg_3632_, v___y_3633_, v___y_3634_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___boxed(lean_object* v_00_u03b1_3637_, lean_object* v_msg_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5(v_00_u03b1_3637_, v_msg_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8(lean_object* v_msgData_3643_, lean_object* v_macroStack_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_msgData_3643_, v_macroStack_3644_, v___y_3646_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___boxed(lean_object* v_msgData_3649_, lean_object* v_macroStack_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8(v_msgData_3649_, v_macroStack_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3662_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3663_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
v___x_3664_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1));
v___x_3665_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
v___x_3666_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3662_, v___x_3663_, v___x_3664_, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
return v_res_3668_;
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
