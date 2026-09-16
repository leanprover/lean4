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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
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
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_nbuckets_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_771_ = lean_array_get_size(v_data_770_);
v___x_772_ = lean_unsigned_to_nat(2u);
v_nbuckets_773_ = lean_nat_mul(v___x_771_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_box(0);
v___x_776_ = lean_mk_array(v_nbuckets_773_, v___x_775_);
v___x_777_ = lean_array_propagate_mark(v_data_770_, v___x_776_);
v___x_778_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_774_, v_data_770_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
else
{
lean_object* v_key_782_; lean_object* v_tail_783_; uint8_t v___x_784_; 
v_key_782_ = lean_ctor_get(v_x_780_, 0);
v_tail_783_ = lean_ctor_get(v_x_780_, 2);
v___x_784_ = lean_name_eq(v_key_782_, v_a_779_);
if (v___x_784_ == 0)
{
v_x_780_ = v_tail_783_;
goto _start;
}
else
{
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec(v_a_786_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object* v_m_790_, lean_object* v_a_791_, lean_object* v_b_792_){
_start:
{
lean_object* v_size_793_; lean_object* v_buckets_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_840_; 
v_size_793_ = lean_ctor_get(v_m_790_, 0);
v_buckets_794_ = lean_ctor_get(v_m_790_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_m_790_);
if (v_isSharedCheck_840_ == 0)
{
v___x_796_ = v_m_790_;
v_isShared_797_ = v_isSharedCheck_840_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_buckets_794_);
lean_inc(v_size_793_);
lean_dec(v_m_790_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_840_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; uint64_t v___y_800_; 
v___x_798_ = lean_array_get_size(v_buckets_794_);
if (lean_obj_tag(v_a_791_) == 0)
{
uint64_t v___x_838_; 
v___x_838_ = 1723ULL;
v___y_800_ = v___x_838_;
goto v___jp_799_;
}
else
{
uint64_t v_hash_839_; 
v_hash_839_ = lean_ctor_get_uint64(v_a_791_, sizeof(void*)*2);
v___y_800_ = v_hash_839_;
goto v___jp_799_;
}
v___jp_799_:
{
uint64_t v___x_801_; uint64_t v___x_802_; uint64_t v_fold_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v_bkt_812_; uint8_t v___x_813_; 
v___x_801_ = 32ULL;
v___x_802_ = lean_uint64_shift_right(v___y_800_, v___x_801_);
v_fold_803_ = lean_uint64_xor(v___y_800_, v___x_802_);
v___x_804_ = 16ULL;
v___x_805_ = lean_uint64_shift_right(v_fold_803_, v___x_804_);
v___x_806_ = lean_uint64_xor(v_fold_803_, v___x_805_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = lean_usize_of_nat(v___x_798_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_sub(v___x_808_, v___x_809_);
v___x_811_ = lean_usize_land(v___x_807_, v___x_810_);
v_bkt_812_ = lean_array_uget_borrowed(v_buckets_794_, v___x_811_);
v___x_813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_791_, v_bkt_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v_size_x27_815_; lean_object* v___x_816_; lean_object* v_buckets_x27_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_814_ = lean_unsigned_to_nat(1u);
v_size_x27_815_ = lean_nat_add(v_size_793_, v___x_814_);
lean_dec(v_size_793_);
lean_inc(v_bkt_812_);
v___x_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_816_, 0, v_a_791_);
lean_ctor_set(v___x_816_, 1, v_b_792_);
lean_ctor_set(v___x_816_, 2, v_bkt_812_);
v_buckets_x27_817_ = lean_array_uset(v_buckets_794_, v___x_811_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(4u);
v___x_819_ = lean_nat_mul(v_size_x27_815_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(3u);
v___x_821_ = lean_nat_div(v___x_819_, v___x_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_array_get_size(v_buckets_x27_817_);
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
if (v___x_823_ == 0)
{
lean_object* v_val_824_; lean_object* v___x_826_; 
v_val_824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_817_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_val_824_);
lean_ctor_set(v___x_796_, 0, v_size_x27_815_);
v___x_826_ = v___x_796_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_size_x27_815_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v___x_829_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_buckets_x27_817_);
lean_ctor_set(v___x_796_, 0, v_size_x27_815_);
v___x_829_ = v___x_796_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_size_x27_815_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_buckets_x27_817_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v___x_831_; lean_object* v_buckets_x27_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_bkt_812_);
v___x_831_ = lean_box(0);
v_buckets_x27_832_ = lean_array_uset(v_buckets_794_, v___x_811_, v___x_831_);
v___x_833_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_791_, v_b_792_, v_bkt_812_);
v___x_834_ = lean_array_uset(v_buckets_x27_832_, v___x_811_, v___x_833_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_834_);
v___x_836_ = v___x_796_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_793_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object* v_as_x27_841_, lean_object* v_b_842_){
_start:
{
if (lean_obj_tag(v_as_x27_841_) == 0)
{
return v_b_842_;
}
else
{
lean_object* v_head_843_; lean_object* v_tail_844_; lean_object* v_fst_845_; lean_object* v_snd_846_; lean_object* v_r_847_; 
v_head_843_ = lean_ctor_get(v_as_x27_841_, 0);
v_tail_844_ = lean_ctor_get(v_as_x27_841_, 1);
v_fst_845_ = lean_ctor_get(v_head_843_, 0);
v_snd_846_ = lean_ctor_get(v_head_843_, 1);
lean_inc(v_snd_846_);
lean_inc(v_fst_845_);
v_r_847_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_842_, v_fst_845_, v_snd_846_);
v_as_x27_841_ = v_tail_844_;
v_b_842_ = v_r_847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_849_, lean_object* v_b_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_849_, v_b_850_);
lean_dec(v_as_x27_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* v_m_852_, lean_object* v_l_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_853_, v_m_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object* v_m_855_, lean_object* v_l_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(v_m_855_, v_l_856_);
lean_dec(v_l_856_);
return v_res_857_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = lean_box(0);
v___x_921_ = lean_unsigned_to_nat(16u);
v___x_922_ = lean_mk_array(v___x_921_, v___x_920_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21));
v___x_928_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_m_931_, lean_object* v_a_932_, lean_object* v_b_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_931_, v_a_932_, v_b_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object* v_as_935_, lean_object* v_as_x27_936_, lean_object* v_b_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_936_, v_b_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object* v_as_940_, lean_object* v_as_x27_941_, lean_object* v_b_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_940_, v_as_x27_941_, v_b_942_, v_a_943_);
lean_dec(v_as_x27_941_);
lean_dec(v_as_940_);
return v_res_944_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_945_, lean_object* v_a_946_, lean_object* v_x_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_946_, v_x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_949_, lean_object* v_a_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_949_, v_a_950_, v_x_951_);
lean_dec(v_x_951_);
lean_dec(v_a_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_954_, lean_object* v_data_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_957_, lean_object* v_a_958_, lean_object* v_b_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_958_, v_b_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_962_, lean_object* v_i_963_, lean_object* v_source_964_, lean_object* v_target_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_963_, v_source_964_, v_target_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_968_, v_x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object* v_name_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_env_976_; lean_object* v___x_977_; lean_object* v_toEnvExtension_978_; lean_object* v_asyncMode_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_974_ = lean_box(1);
v___x_975_ = lean_st_ref_get(v___y_972_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
v___x_977_ = l_Lean_errorExplanationExt;
v_toEnvExtension_978_ = lean_ctor_get(v___x_977_, 0);
v_asyncMode_979_ = lean_ctor_get(v_toEnvExtension_978_, 2);
v___x_980_ = lean_box(0);
v___x_981_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_974_, v___x_977_, v_env_976_, v_asyncMode_979_, v___x_980_);
v___x_982_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_981_, v_name_971_);
lean_dec(v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object* v_name_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec(v_name_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object* v_name_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_988_, v___y_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object* v_name_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v_name_997_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(lean_object* v_msgData_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v_env_1013_; lean_object* v___x_1014_; lean_object* v_toCold_1015_; lean_object* v_mctx_1016_; lean_object* v_lctx_1017_; lean_object* v_options_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1012_ = lean_st_ref_get(v___y_1010_);
v_env_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_ref(v_env_1013_);
lean_dec(v___x_1012_);
v___x_1014_ = lean_st_ref_get(v___y_1008_);
v_toCold_1015_ = lean_ctor_get(v___y_1009_, 0);
v_mctx_1016_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_ref(v_mctx_1016_);
lean_dec(v___x_1014_);
v_lctx_1017_ = lean_ctor_get(v___y_1007_, 2);
v_options_1018_ = lean_ctor_get(v_toCold_1015_, 2);
lean_inc_ref(v_options_1018_);
lean_inc_ref(v_lctx_1017_);
v___x_1019_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1019_, 0, v_env_1013_);
lean_ctor_set(v___x_1019_, 1, v_mctx_1016_);
lean_ctor_set(v___x_1019_, 2, v_lctx_1017_);
lean_ctor_set(v___x_1019_, 3, v_options_1018_);
v___x_1020_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_msgData_1006_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(lean_object* v_msgData_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1029_; double v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_float_of_nat(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object* v_cls_1034_, lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_ref_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1087_; 
v_ref_1041_ = lean_ctor_get(v___y_1038_, 2);
v___x_1042_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1087_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1087_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v_traceState_1048_; lean_object* v_env_1049_; lean_object* v_nextMacroScope_1050_; lean_object* v_ngen_1051_; lean_object* v_auxDeclNGen_1052_; lean_object* v_cache_1053_; lean_object* v_messages_1054_; lean_object* v_infoState_1055_; lean_object* v_snapshotTasks_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1086_; 
v___x_1047_ = lean_st_ref_take(v___y_1039_);
v_traceState_1048_ = lean_ctor_get(v___x_1047_, 4);
v_env_1049_ = lean_ctor_get(v___x_1047_, 0);
v_nextMacroScope_1050_ = lean_ctor_get(v___x_1047_, 1);
v_ngen_1051_ = lean_ctor_get(v___x_1047_, 2);
v_auxDeclNGen_1052_ = lean_ctor_get(v___x_1047_, 3);
v_cache_1053_ = lean_ctor_get(v___x_1047_, 5);
v_messages_1054_ = lean_ctor_get(v___x_1047_, 6);
v_infoState_1055_ = lean_ctor_get(v___x_1047_, 7);
v_snapshotTasks_1056_ = lean_ctor_get(v___x_1047_, 8);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1058_ = v___x_1047_;
v_isShared_1059_ = v_isSharedCheck_1086_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_snapshotTasks_1056_);
lean_inc(v_infoState_1055_);
lean_inc(v_messages_1054_);
lean_inc(v_cache_1053_);
lean_inc(v_traceState_1048_);
lean_inc(v_auxDeclNGen_1052_);
lean_inc(v_ngen_1051_);
lean_inc(v_nextMacroScope_1050_);
lean_inc(v_env_1049_);
lean_dec(v___x_1047_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1086_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
uint64_t v_tid_1060_; lean_object* v_traces_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1085_; 
v_tid_1060_ = lean_ctor_get_uint64(v_traceState_1048_, sizeof(void*)*1);
v_traces_1061_ = lean_ctor_get(v_traceState_1048_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_traceState_1048_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1063_ = v_traceState_1048_;
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_traces_1061_);
lean_dec(v_traceState_1048_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; double v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_1068_ = 0;
v___x_1069_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1070_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1070_, 0, v_cls_1034_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set_float(v___x_1070_, sizeof(void*)*3, v___x_1067_);
lean_ctor_set_float(v___x_1070_, sizeof(void*)*3 + 8, v___x_1067_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*3 + 16, v___x_1068_);
v___x_1071_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_1072_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v_a_1043_);
lean_ctor_set(v___x_1072_, 2, v___x_1071_);
lean_inc(v_ref_1041_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_ref_1041_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_PersistentArray_push___redArg(v_traces_1061_, v___x_1073_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1074_);
v___x_1076_ = v___x_1063_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1074_);
lean_ctor_set_uint64(v_reuseFailAlloc_1084_, sizeof(void*)*1, v_tid_1060_);
v___x_1076_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___x_1076_);
v___x_1078_ = v___x_1058_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_env_1049_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_nextMacroScope_1050_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_ngen_1051_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_auxDeclNGen_1052_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_cache_1053_);
lean_ctor_set(v_reuseFailAlloc_1083_, 6, v_messages_1054_);
lean_ctor_set(v_reuseFailAlloc_1083_, 7, v_infoState_1055_);
lean_ctor_set(v_reuseFailAlloc_1083_, 8, v_snapshotTasks_1056_);
v___x_1078_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_st_ref_put(v___y_1039_, v___x_1078_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1065_);
v___x_1081_ = v___x_1045_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1065_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object* v_cls_1088_, lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1088_, v_msg_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object* v_as_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
if (lean_obj_tag(v_as_1099_) == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v_toCold_1109_; lean_object* v_options_1110_; uint8_t v_hasTrace_1111_; 
v_toCold_1109_ = lean_ctor_get(v___y_1104_, 0);
v_options_1110_ = lean_ctor_get(v_toCold_1109_, 2);
v_hasTrace_1111_ = lean_ctor_get_uint8(v_options_1110_, sizeof(void*)*1);
if (v_hasTrace_1111_ == 0)
{
lean_object* v_tail_1112_; 
v_tail_1112_ = lean_ctor_get(v_as_1099_, 1);
lean_inc(v_tail_1112_);
lean_dec_ref_known(v_as_1099_, 2);
v_as_1099_ = v_tail_1112_;
goto _start;
}
else
{
lean_object* v_head_1114_; lean_object* v_tail_1115_; lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v_inheritedTraceOptions_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_head_1114_ = lean_ctor_get(v_as_1099_, 0);
lean_inc(v_head_1114_);
v_tail_1115_ = lean_ctor_get(v_as_1099_, 1);
lean_inc(v_tail_1115_);
lean_dec_ref_known(v_as_1099_, 2);
v_fst_1116_ = lean_ctor_get(v_head_1114_, 0);
lean_inc_n(v_fst_1116_, 2);
v_snd_1117_ = lean_ctor_get(v_head_1114_, 1);
lean_inc(v_snd_1117_);
lean_dec(v_head_1114_);
v_inheritedTraceOptions_1118_ = lean_ctor_get(v_toCold_1109_, 11);
v___x_1119_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1120_ = l_Lean_Name_append(v___x_1119_, v_fst_1116_);
v___x_1121_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1118_, v_options_1110_, v___x_1120_);
lean_dec(v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec(v_snd_1117_);
lean_dec(v_fst_1116_);
v_as_1099_ = v_tail_1115_;
goto _start;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_snd_1117_);
v___x_1124_ = l_Lean_MessageData_ofFormat(v___x_1123_);
v___x_1125_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_1116_, v___x_1124_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_dec_ref_known(v___x_1125_, 1);
v_as_1099_ = v_tail_1115_;
goto _start;
}
else
{
lean_dec(v_tail_1115_);
return v___x_1125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object* v_as_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1135_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v_res_1143_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l_Lean_maxRecDepthErrorMessage;
v___x_1150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
v___x_1152_ = l_Lean_MessageData_ofFormat(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
v___x_1154_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2));
v___x_1155_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object* v_ref_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_ref_1156_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object* v_env_1164_, lean_object* v_declName_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___x_1168_; lean_object* v_env_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1168_ = 0;
v_env_1169_ = l_Lean_Environment_setExporting(v_env_1164_, v___x_1168_);
lean_inc(v_declName_1165_);
v___x_1170_ = l_Lean_mkPrivateName(v_env_1169_, v_declName_1165_);
v___x_1171_ = 1;
lean_inc_ref(v_env_1169_);
v___x_1172_ = l_Lean_Environment_contains(v_env_1169_, v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = l_Lean_privateToUserName(v_declName_1165_);
v___x_1174_ = l_Lean_Environment_contains(v_env_1169_, v___x_1173_, v___x_1171_);
v___x_1175_ = lean_box(v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___y_1167_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_env_1169_);
lean_dec(v_declName_1165_);
v___x_1177_ = lean_box(v___x_1172_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___y_1167_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object* v_env_1179_, lean_object* v_declName_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_1179_, v_declName_1180_, v___y_1181_, v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object* v_x_1184_, lean_object* v___y_1185_){
_start:
{
if (lean_obj_tag(v_x_1184_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v_x_1184_, 0);
lean_inc(v_a_1186_);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1186_);
lean_ctor_set(v___x_1187_, 1, v___y_1185_);
return v___x_1187_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_ctor_get(v_x_1184_, 0);
lean_inc(v_a_1188_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1188_);
lean_ctor_set(v___x_1189_, 1, v___y_1185_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object* v_x_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_1190_, v___y_1191_);
lean_dec_ref(v_x_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object* v_env_1193_, lean_object* v_stx_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1193_, v_stx_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
if (lean_obj_tag(v_a_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_a_1199_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1197_, 0);
lean_dec(v_unused_1208_);
v___x_1201_ = v___x_1197_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(0);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_a_1199_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1237_; 
v_val_1209_ = lean_ctor_get(v_a_1198_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_a_1198_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1211_ = v_a_1198_;
v_isShared_1212_ = v_isSharedCheck_1237_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_val_1209_);
lean_dec(v_a_1198_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1237_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_snd_1213_; 
v_snd_1213_ = lean_ctor_get(v_val_1209_, 1);
lean_inc(v_snd_1213_);
lean_dec(v_val_1209_);
if (lean_obj_tag(v_snd_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1211_);
v_a_1214_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1197_, 2);
v_a_1215_ = lean_ctor_get(v_snd_1213_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_snd_1213_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_snd_1213_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v_snd_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1220_, v_a_1214_);
lean_dec_ref(v___x_1220_);
return v___x_1221_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_a_1224_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1197_, 2);
v_a_1225_ = lean_ctor_get(v_snd_1213_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_snd_1213_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1227_ = v_snd_1213_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v_snd_1213_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_a_1225_);
v___x_1230_ = v___x_1211_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1232_, v_a_1224_);
lean_dec_ref(v___x_1232_);
return v___x_1233_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1238_ = lean_ctor_get(v___x_1197_, 0);
v_a_1239_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1197_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_inc(v_a_1238_);
lean_dec(v___x_1197_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1238_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object* v_env_1247_, lean_object* v_stx_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_1247_, v_stx_1248_, v___y_1249_, v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object* v_env_1252_, lean_object* v_options_1253_, lean_object* v_currNamespace_1254_, lean_object* v_openDecls_1255_, lean_object* v_n_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = l_Lean_ResolveName_resolveGlobalName(v_env_1252_, v_options_1253_, v_currNamespace_1254_, v_openDecls_1255_, v_n_1256_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object* v_env_1261_, lean_object* v_options_1262_, lean_object* v_currNamespace_1263_, lean_object* v_openDecls_1264_, lean_object* v_n_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_1261_, v_options_1262_, v_currNamespace_1263_, v_openDecls_1264_, v_n_1265_, v___y_1266_, v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec_ref(v_options_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object* v_currNamespace_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_currNamespace_1269_);
lean_ctor_set(v___x_1272_, 1, v___y_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_1273_, v___y_1274_, v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object* v_a_1277_, lean_object* v_x_1278_){
_start:
{
if (lean_obj_tag(v_x_1278_) == 0)
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_box(0);
return v___x_1279_;
}
else
{
lean_object* v_key_1280_; lean_object* v_value_1281_; lean_object* v_tail_1282_; uint8_t v___x_1283_; 
v_key_1280_ = lean_ctor_get(v_x_1278_, 0);
v_value_1281_ = lean_ctor_get(v_x_1278_, 1);
v_tail_1282_ = lean_ctor_get(v_x_1278_, 2);
v___x_1283_ = lean_name_eq(v_key_1280_, v_a_1277_);
if (v___x_1283_ == 0)
{
v_x_1278_ = v_tail_1282_;
goto _start;
}
else
{
lean_object* v___x_1285_; 
lean_inc(v_value_1281_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_value_1281_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object* v_a_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1286_, v_x_1287_);
lean_dec(v_x_1287_);
lean_dec(v_a_1286_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object* v_m_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_buckets_1291_; lean_object* v___x_1292_; uint64_t v___y_1294_; 
v_buckets_1291_ = lean_ctor_get(v_m_1289_, 1);
v___x_1292_ = lean_array_get_size(v_buckets_1291_);
if (lean_obj_tag(v_a_1290_) == 0)
{
uint64_t v___x_1308_; 
v___x_1308_ = 1723ULL;
v___y_1294_ = v___x_1308_;
goto v___jp_1293_;
}
else
{
uint64_t v_hash_1309_; 
v_hash_1309_ = lean_ctor_get_uint64(v_a_1290_, sizeof(void*)*2);
v___y_1294_ = v_hash_1309_;
goto v___jp_1293_;
}
v___jp_1293_:
{
uint64_t v___x_1295_; uint64_t v___x_1296_; uint64_t v_fold_1297_; uint64_t v___x_1298_; uint64_t v___x_1299_; uint64_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1295_ = 32ULL;
v___x_1296_ = lean_uint64_shift_right(v___y_1294_, v___x_1295_);
v_fold_1297_ = lean_uint64_xor(v___y_1294_, v___x_1296_);
v___x_1298_ = 16ULL;
v___x_1299_ = lean_uint64_shift_right(v_fold_1297_, v___x_1298_);
v___x_1300_ = lean_uint64_xor(v_fold_1297_, v___x_1299_);
v___x_1301_ = lean_uint64_to_usize(v___x_1300_);
v___x_1302_ = lean_usize_of_nat(v___x_1292_);
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_sub(v___x_1302_, v___x_1303_);
v___x_1305_ = lean_usize_land(v___x_1301_, v___x_1304_);
v___x_1306_ = lean_array_uget_borrowed(v_buckets_1291_, v___x_1305_);
v___x_1307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1290_, v___x_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object* v_m_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_m_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object* v_keys_1313_, lean_object* v_i_1314_, lean_object* v_k_1315_){
_start:
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_array_get_size(v_keys_1313_);
v___x_1317_ = lean_nat_dec_lt(v_i_1314_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec(v_i_1314_);
return v___x_1317_;
}
else
{
lean_object* v_k_x27_1318_; uint8_t v___x_1319_; 
v_k_x27_1318_ = lean_array_fget_borrowed(v_keys_1313_, v_i_1314_);
v___x_1319_ = l_Lean_instBEqExtraModUse_beq(v_k_1315_, v_k_x27_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_i_1314_, v___x_1320_);
lean_dec(v_i_1314_);
v_i_1314_ = v___x_1321_;
goto _start;
}
else
{
lean_dec(v_i_1314_);
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object* v_keys_1323_, lean_object* v_i_1324_, lean_object* v_k_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_1323_, v_i_1324_, v_k_1325_);
lean_dec_ref(v_k_1325_);
lean_dec_ref(v_keys_1323_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object* v_x_1328_, size_t v_x_1329_, lean_object* v_x_1330_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 0)
{
lean_object* v_es_1331_; lean_object* v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; lean_object* v_j_1335_; lean_object* v___x_1336_; 
v_es_1331_ = lean_ctor_get(v_x_1328_, 0);
v___x_1332_ = lean_box(2);
v___x_1333_ = ((size_t)31ULL);
v___x_1334_ = lean_usize_land(v_x_1329_, v___x_1333_);
v_j_1335_ = lean_usize_to_nat(v___x_1334_);
v___x_1336_ = lean_array_get_borrowed(v___x_1332_, v_es_1331_, v_j_1335_);
lean_dec(v_j_1335_);
switch(lean_obj_tag(v___x_1336_))
{
case 0:
{
lean_object* v_key_1337_; uint8_t v___x_1338_; 
v_key_1337_ = lean_ctor_get(v___x_1336_, 0);
v___x_1338_ = l_Lean_instBEqExtraModUse_beq(v_x_1330_, v_key_1337_);
return v___x_1338_;
}
case 1:
{
lean_object* v_node_1339_; size_t v___x_1340_; size_t v___x_1341_; 
v_node_1339_ = lean_ctor_get(v___x_1336_, 0);
v___x_1340_ = ((size_t)5ULL);
v___x_1341_ = lean_usize_shift_right(v_x_1329_, v___x_1340_);
v_x_1328_ = v_node_1339_;
v_x_1329_ = v___x_1341_;
goto _start;
}
default: 
{
uint8_t v___x_1343_; 
v___x_1343_ = 0;
return v___x_1343_;
}
}
}
else
{
lean_object* v_ks_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_ks_1344_ = lean_ctor_get(v_x_1328_, 0);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_1344_, v___x_1345_, v_x_1330_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
size_t v_x_20449__boxed_1350_; uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_x_20449__boxed_1350_ = lean_unbox_usize(v_x_1348_);
lean_dec(v_x_1348_);
v_res_1351_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1347_, v_x_20449__boxed_1350_, v_x_1349_);
lean_dec_ref(v_x_1349_);
lean_dec_ref(v_x_1347_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
uint64_t v___x_1355_; size_t v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = l_Lean_instHashableExtraModUse_hash(v_x_1354_);
v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
v___x_1357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1353_, v___x_1356_, v_x_1354_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_1358_, v_x_1359_);
lean_dec_ref(v_x_1359_);
lean_dec_ref(v_x_1358_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1362_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1363_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
v___x_1369_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_ctor_set(v___x_1369_, 2, v___x_1368_);
lean_ctor_set(v___x_1369_, 3, v___x_1368_);
lean_ctor_set(v___x_1369_, 4, v___x_1368_);
lean_ctor_set(v___x_1369_, 5, v___x_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7));
v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_cls_1381_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6));
v___x_1382_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1383_ = l_Lean_Name_append(v___x_1382_, v_cls_1381_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object* v_mod_1394_, uint8_t v_isMeta_1395_, lean_object* v_hint_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_env_1406_; uint8_t v_isExporting_1407_; lean_object* v_entry_1408_; lean_object* v___x_1409_; lean_object* v_env_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1404_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0);
v___x_1405_ = lean_st_ref_get(v___y_1402_);
v_env_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_env_1406_);
lean_dec(v___x_1405_);
v_isExporting_1407_ = lean_ctor_get_uint8(v_env_1406_, sizeof(void*)*8);
lean_dec_ref(v_env_1406_);
lean_inc(v_mod_1394_);
v_entry_1408_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1408_, 0, v_mod_1394_);
lean_ctor_set_uint8(v_entry_1408_, sizeof(void*)*1, v_isExporting_1407_);
lean_ctor_set_uint8(v_entry_1408_, sizeof(void*)*1 + 1, v_isMeta_1395_);
v___x_1409_ = lean_st_ref_get(v___y_1402_);
v_env_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_env_1410_);
lean_dec(v___x_1409_);
v___x_1411_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1412_ = lean_box(1);
v___x_1413_ = lean_box(0);
v___x_1456_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1404_, v___x_1411_, v_env_1410_, v___x_1412_, v___x_1413_);
v___x_1457_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_1456_, v_entry_1408_);
lean_dec(v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v_toCold_1458_; lean_object* v_options_1459_; uint8_t v_hasTrace_1460_; 
v_toCold_1458_ = lean_ctor_get(v___y_1401_, 0);
v_options_1459_ = lean_ctor_get(v_toCold_1458_, 2);
v_hasTrace_1460_ = lean_ctor_get_uint8(v_options_1459_, sizeof(void*)*1);
if (v_hasTrace_1460_ == 0)
{
lean_dec(v_hint_1396_);
lean_dec(v_mod_1394_);
v___y_1415_ = v___y_1400_;
v___y_1416_ = v___y_1402_;
goto v___jp_1414_;
}
else
{
lean_object* v_inheritedTraceOptions_1461_; lean_object* v_cls_1462_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v_inheritedTraceOptions_1461_ = lean_ctor_get(v_toCold_1458_, 11);
v_cls_1462_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6));
v___x_1482_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_1483_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1461_, v_options_1459_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_dec(v_hint_1396_);
lean_dec(v_mod_1394_);
v___y_1415_ = v___y_1400_;
v___y_1416_ = v___y_1402_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1484_; lean_object* v___y_1486_; 
v___x_1484_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
if (v_isExporting_1407_ == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_1486_ = v___x_1493_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_1486_ = v___x_1494_;
goto v___jp_1485_;
}
v___jp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_inc_ref(v___y_1486_);
v___x_1487_ = l_Lean_stringToMessageData(v___y_1486_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1484_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
if (v_isMeta_1395_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___y_1469_ = v___x_1490_;
v___y_1470_ = v___x_1491_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1492_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18));
v___y_1469_ = v___x_1490_;
v___y_1470_ = v___x_1492_;
goto v___jp_1468_;
}
}
}
v___jp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1464_);
lean_ctor_set(v___x_1466_, 1, v___y_1465_);
v___x_1467_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1462_, v___x_1466_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref_known(v___x_1467_, 1);
v___y_1415_ = v___y_1400_;
v___y_1416_ = v___y_1402_;
goto v___jp_1414_;
}
else
{
lean_dec_ref_known(v_entry_1408_, 1);
return v___x_1467_;
}
}
v___jp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
lean_inc_ref(v___y_1470_);
v___x_1471_ = l_Lean_stringToMessageData(v___y_1470_);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1469_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_MessageData_ofName(v_mod_1394_);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_Name_isAnonymous(v_hint_1396_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_1479_ = l_Lean_MessageData_ofName(v_hint_1396_);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___y_1464_ = v___x_1476_;
v___y_1465_ = v___x_1480_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1481_; 
lean_dec(v_hint_1396_);
v___x_1481_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11);
v___y_1464_ = v___x_1476_;
v___y_1465_ = v___x_1481_;
goto v___jp_1463_;
}
}
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref_known(v_entry_1408_, 1);
lean_dec(v_hint_1396_);
lean_dec(v_mod_1394_);
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
v___jp_1414_:
{
lean_object* v___x_1417_; lean_object* v_toEnvExtension_1418_; lean_object* v_env_1419_; lean_object* v_nextMacroScope_1420_; lean_object* v_ngen_1421_; lean_object* v_auxDeclNGen_1422_; lean_object* v_traceState_1423_; lean_object* v_messages_1424_; lean_object* v_infoState_1425_; lean_object* v_snapshotTasks_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1454_; 
v___x_1417_ = lean_st_ref_take(v___y_1416_);
v_toEnvExtension_1418_ = lean_ctor_get(v___x_1411_, 0);
v_env_1419_ = lean_ctor_get(v___x_1417_, 0);
v_nextMacroScope_1420_ = lean_ctor_get(v___x_1417_, 1);
v_ngen_1421_ = lean_ctor_get(v___x_1417_, 2);
v_auxDeclNGen_1422_ = lean_ctor_get(v___x_1417_, 3);
v_traceState_1423_ = lean_ctor_get(v___x_1417_, 4);
v_messages_1424_ = lean_ctor_get(v___x_1417_, 6);
v_infoState_1425_ = lean_ctor_get(v___x_1417_, 7);
v_snapshotTasks_1426_ = lean_ctor_get(v___x_1417_, 8);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1417_, 5);
lean_dec(v_unused_1455_);
v___x_1428_ = v___x_1417_;
v_isShared_1429_ = v_isSharedCheck_1454_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_snapshotTasks_1426_);
lean_inc(v_infoState_1425_);
lean_inc(v_messages_1424_);
lean_inc(v_traceState_1423_);
lean_inc(v_auxDeclNGen_1422_);
lean_inc(v_ngen_1421_);
lean_inc(v_nextMacroScope_1420_);
lean_inc(v_env_1419_);
lean_dec(v___x_1417_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1454_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_asyncMode_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v_asyncMode_1430_ = lean_ctor_get(v_toEnvExtension_1418_, 2);
v___x_1431_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1411_, v_env_1419_, v_entry_1408_, v_asyncMode_1430_, v___x_1413_);
v___x_1432_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 5, v___x_1432_);
lean_ctor_set(v___x_1428_, 0, v___x_1431_);
v___x_1434_ = v___x_1428_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_nextMacroScope_1420_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_ngen_1421_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_auxDeclNGen_1422_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_traceState_1423_);
lean_ctor_set(v_reuseFailAlloc_1453_, 5, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1453_, 6, v_messages_1424_);
lean_ctor_set(v_reuseFailAlloc_1453_, 7, v_infoState_1425_);
lean_ctor_set(v_reuseFailAlloc_1453_, 8, v_snapshotTasks_1426_);
v___x_1434_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_mctx_1437_; lean_object* v_zetaDeltaFVarIds_1438_; lean_object* v_postponed_1439_; lean_object* v_diag_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1451_; 
v___x_1435_ = lean_st_ref_put(v___y_1416_, v___x_1434_);
v___x_1436_ = lean_st_ref_take(v___y_1415_);
v_mctx_1437_ = lean_ctor_get(v___x_1436_, 0);
v_zetaDeltaFVarIds_1438_ = lean_ctor_get(v___x_1436_, 2);
v_postponed_1439_ = lean_ctor_get(v___x_1436_, 3);
v_diag_1440_ = lean_ctor_get(v___x_1436_, 4);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1436_, 1);
lean_dec(v_unused_1452_);
v___x_1442_ = v___x_1436_;
v_isShared_1443_ = v_isSharedCheck_1451_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_diag_1440_);
lean_inc(v_postponed_1439_);
lean_inc(v_zetaDeltaFVarIds_1438_);
lean_inc(v_mctx_1437_);
lean_dec(v___x_1436_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1451_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1445_);
v___x_1447_ = v___x_1442_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_mctx_1437_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_zetaDeltaFVarIds_1438_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_postponed_1439_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_diag_1440_);
v___x_1447_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_st_ref_put(v___y_1415_, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1444_);
return v___x_1449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_1497_, lean_object* v_isMeta_1498_, lean_object* v_hint_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v_isMeta_boxed_1507_; lean_object* v_res_1508_; 
v_isMeta_boxed_1507_ = lean_unbox(v_isMeta_1498_);
v_res_1508_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_1497_, v_isMeta_boxed_1507_, v_hint_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object* v___x_1509_, lean_object* v_declName_1510_, lean_object* v_as_1511_, size_t v_sz_1512_, size_t v_i_1513_, lean_object* v_b_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1513_, v_sz_1512_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_dec(v_declName_1510_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1514_);
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; lean_object* v_modules_1525_; lean_object* v___x_1526_; lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v_toImport_1529_; lean_object* v_module_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1524_ = l_Lean_Environment_header(v___x_1509_);
v_modules_1525_ = lean_ctor_get(v___x_1524_, 3);
lean_inc_ref(v_modules_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1527_ = lean_array_uget_borrowed(v_as_1511_, v_i_1513_);
v___x_1528_ = lean_array_get(v___x_1526_, v_modules_1525_, v_a_1527_);
lean_dec_ref(v_modules_1525_);
v_toImport_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc_ref(v_toImport_1529_);
lean_dec(v___x_1528_);
v_module_1530_ = lean_ctor_get(v_toImport_1529_, 0);
lean_inc(v_module_1530_);
lean_dec_ref(v_toImport_1529_);
v___x_1531_ = lean_box(0);
v___x_1532_ = 0;
lean_inc(v_declName_1510_);
v___x_1533_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1530_, v___x_1532_, v_declName_1510_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1533_) == 0)
{
size_t v___x_1534_; size_t v___x_1535_; 
lean_dec_ref_known(v___x_1533_, 1);
v___x_1534_ = ((size_t)1ULL);
v___x_1535_ = lean_usize_add(v_i_1513_, v___x_1534_);
v_i_1513_ = v___x_1535_;
v_b_1514_ = v___x_1531_;
goto _start;
}
else
{
lean_dec(v_declName_1510_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1537_, lean_object* v_declName_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
size_t v_sz_boxed_1550_; size_t v_i_boxed_1551_; lean_object* v_res_1552_; 
v_sz_boxed_1550_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1551_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_1537_, v_declName_1538_, v_as_1539_, v_sz_boxed_1550_, v_i_boxed_1551_, v_b_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_as_1539_);
lean_dec_ref(v___x_1537_);
return v_res_1552_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object* v_declName_1556_, uint8_t v_isMeta_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_env_1570_; lean_object* v___y_1572_; lean_object* v___x_1585_; 
v___x_1565_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0);
v___x_1566_ = lean_st_ref_get(v___y_1563_);
v_env_1570_ = lean_ctor_get(v___x_1566_, 0);
lean_inc_ref(v_env_1570_);
lean_dec(v___x_1566_);
v___x_1585_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1570_, v_declName_1556_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_dec_ref(v_env_1570_);
lean_dec(v_declName_1556_);
goto v___jp_1567_;
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1587_; lean_object* v_modules_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_val_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = l_Lean_Environment_header(v_env_1570_);
v_modules_1588_ = lean_ctor_get(v___x_1587_, 3);
lean_inc_ref(v_modules_1588_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = lean_array_get_size(v_modules_1588_);
v___x_1590_ = lean_nat_dec_lt(v_val_1586_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v_modules_1588_);
lean_dec(v_val_1586_);
lean_dec_ref(v_env_1570_);
lean_dec(v_declName_1556_);
goto v___jp_1567_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___y_1594_; 
v___x_1591_ = lean_array_fget(v_modules_1588_, v_val_1586_);
lean_dec(v_val_1586_);
lean_dec_ref(v_modules_1588_);
v___x_1592_ = lean_st_ref_get(v___y_1563_);
if (v_isMeta_1557_ == 0)
{
lean_dec(v___x_1592_);
v___y_1594_ = v_isMeta_1557_;
goto v___jp_1593_;
}
else
{
lean_object* v_env_1605_; uint8_t v___x_1606_; 
v_env_1605_ = lean_ctor_get(v___x_1592_, 0);
lean_inc_ref(v_env_1605_);
lean_dec(v___x_1592_);
lean_inc(v_declName_1556_);
v___x_1606_ = l_Lean_isMarkedMeta(v_env_1605_, v_declName_1556_);
if (v___x_1606_ == 0)
{
v___y_1594_ = v_isMeta_1557_;
goto v___jp_1593_;
}
else
{
uint8_t v___x_1607_; 
v___x_1607_ = 0;
v___y_1594_ = v___x_1607_;
goto v___jp_1593_;
}
}
v___jp_1593_:
{
lean_object* v_toImport_1595_; lean_object* v_module_1596_; lean_object* v___x_1597_; 
v_toImport_1595_ = lean_ctor_get(v___x_1591_, 0);
lean_inc_ref(v_toImport_1595_);
lean_dec(v___x_1591_);
v_module_1596_ = lean_ctor_get(v_toImport_1595_, 0);
lean_inc(v_module_1596_);
lean_dec_ref(v_toImport_1595_);
lean_inc(v_declName_1556_);
v___x_1597_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1596_, v___y_1594_, v_declName_1556_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref_known(v___x_1597_, 1);
v___x_1598_ = l_Lean_indirectModUseExt;
v___x_1599_ = lean_box(1);
v___x_1600_ = lean_box(0);
lean_inc_ref(v_env_1570_);
v___x_1601_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1565_, v___x_1598_, v_env_1570_, v___x_1599_, v___x_1600_);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_1601_, v_declName_1556_);
lean_dec(v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___y_1572_ = v___x_1603_;
goto v___jp_1571_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v___x_1602_, 1);
v___y_1572_ = v_val_1604_;
goto v___jp_1571_;
}
}
else
{
lean_dec_ref(v_env_1570_);
lean_dec(v_declName_1556_);
return v___x_1597_;
}
}
}
}
v___jp_1567_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
v___jp_1571_:
{
lean_object* v___x_1573_; size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = lean_box(0);
v_sz_1574_ = lean_array_size(v___y_1572_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_1570_, v_declName_1556_, v___y_1572_, v_sz_1574_, v___x_1575_, v___x_1573_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_env_1570_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1576_, 0);
lean_dec(v_unused_1584_);
v___x_1578_ = v___x_1576_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v___x_1576_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1573_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1573_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object* v_declName_1608_, lean_object* v_isMeta_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v_isMeta_boxed_1617_; lean_object* v_res_1618_; 
v_isMeta_boxed_1617_ = lean_unbox(v_isMeta_1609_);
v_res_1618_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_1608_, v_isMeta_boxed_1617_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object* v_as_x27_1619_, lean_object* v_b_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
if (lean_obj_tag(v_as_x27_1619_) == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_b_1620_);
return v___x_1628_;
}
else
{
lean_object* v_head_1629_; lean_object* v_tail_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; 
v_head_1629_ = lean_ctor_get(v_as_x27_1619_, 0);
v_tail_1630_ = lean_ctor_get(v_as_x27_1619_, 1);
v___x_1631_ = lean_box(0);
v___x_1632_ = 1;
lean_inc(v_head_1629_);
v___x_1633_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_1629_, v___x_1632_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_dec_ref_known(v___x_1633_, 1);
v_as_x27_1619_ = v_tail_1630_;
v_b_1620_ = v___x_1631_;
goto _start;
}
else
{
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1635_, lean_object* v_b_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_1635_, v_b_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v_as_x27_1635_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object* v_env_1645_, lean_object* v_currNamespace_1646_, lean_object* v_openDecls_1647_, lean_object* v_n_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = l_Lean_ResolveName_resolveNamespace(v_env_1645_, v_currNamespace_1646_, v_openDecls_1647_, v_n_1648_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object* v_env_1653_, lean_object* v_currNamespace_1654_, lean_object* v_openDecls_1655_, lean_object* v_n_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_1653_, v_currNamespace_1654_, v_openDecls_1655_, v_n_1656_, v___y_1657_, v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1659_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_box(1);
v___x_1661_ = l_Lean_MessageData_ofFormat(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2));
v___x_1666_ = l_Lean_MessageData_ofFormat(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 0)
{
return v_x_1667_;
}
else
{
lean_object* v_head_1669_; lean_object* v_tail_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1692_; 
v_head_1669_ = lean_ctor_get(v_x_1668_, 0);
v_tail_1670_ = lean_ctor_get(v_x_1668_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1668_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1672_ = v_x_1668_;
v_isShared_1673_ = v_isSharedCheck_1692_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_tail_1670_);
lean_inc(v_head_1669_);
lean_dec(v_x_1668_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1692_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_before_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1690_; 
v_before_1674_ = lean_ctor_get(v_head_1669_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_head_1669_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v_head_1669_, 1);
lean_dec(v_unused_1691_);
v___x_1676_ = v_head_1669_;
v_isShared_1677_ = v_isSharedCheck_1690_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_before_1674_);
lean_dec(v_head_1669_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1690_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 7);
lean_ctor_set(v___x_1676_, 1, v___x_1678_);
lean_ctor_set(v___x_1676_, 0, v_x_1667_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_x_1667_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 7);
lean_ctor_set(v___x_1672_, 1, v___x_1681_);
lean_ctor_set(v___x_1672_, 0, v___x_1680_);
v___x_1683_ = v___x_1672_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_MessageData_ofSyntax(v_before_1674_);
v___x_1685_ = l_Lean_indentD(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1683_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v_x_1667_ = v___x_1686_;
v_x_1668_ = v_tail_1670_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(lean_object* v_opts_1693_, lean_object* v_opt_1694_){
_start:
{
lean_object* v_name_1695_; lean_object* v_defValue_1696_; lean_object* v_map_1697_; lean_object* v___x_1698_; 
v_name_1695_ = lean_ctor_get(v_opt_1694_, 0);
v_defValue_1696_ = lean_ctor_get(v_opt_1694_, 1);
v_map_1697_ = lean_ctor_get(v_opts_1693_, 0);
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1697_, v_name_1695_);
if (lean_obj_tag(v___x_1698_) == 0)
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_unbox(v_defValue_1696_);
return v___x_1699_;
}
else
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1698_, 1);
if (lean_obj_tag(v_val_1700_) == 1)
{
uint8_t v_v_1701_; 
v_v_1701_ = lean_ctor_get_uint8(v_val_1700_, 0);
lean_dec_ref_known(v_val_1700_, 0);
return v_v_1701_;
}
else
{
uint8_t v___x_1702_; 
lean_dec(v_val_1700_);
v___x_1702_ = lean_unbox(v_defValue_1696_);
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(lean_object* v_opts_1703_, lean_object* v_opt_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_1703_, v_opt_1704_);
lean_dec_ref(v_opt_1704_);
lean_dec_ref(v_opts_1703_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1));
v___x_1711_ = l_Lean_MessageData_ofFormat(v___x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(lean_object* v_msgData_1712_, lean_object* v_macroStack_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_toCold_1716_; lean_object* v_options_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_toCold_1716_ = lean_ctor_get(v___y_1714_, 0);
v_options_1717_ = lean_ctor_get(v_toCold_1716_, 2);
v___x_1718_ = l_Lean_Elab_pp_macroStack;
v___x_1719_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_macroStack_1713_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_msgData_1712_);
return v___x_1720_;
}
else
{
if (lean_obj_tag(v_macroStack_1713_) == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_msgData_1712_);
return v___x_1721_;
}
else
{
lean_object* v_head_1722_; lean_object* v_after_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1738_; 
v_head_1722_ = lean_ctor_get(v_macroStack_1713_, 0);
lean_inc(v_head_1722_);
v_after_1723_ = lean_ctor_get(v_head_1722_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_head_1722_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v_head_1722_, 0);
lean_dec(v_unused_1739_);
v___x_1725_ = v_head_1722_;
v_isShared_1726_ = v_isSharedCheck_1738_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_after_1723_);
lean_dec(v_head_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1738_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 7);
lean_ctor_set(v___x_1725_, 1, v___x_1727_);
lean_ctor_set(v___x_1725_, 0, v_msgData_1712_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_msgData_1712_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_msgData_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1730_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_MessageData_ofSyntax(v_after_1723_);
v___x_1733_ = l_Lean_indentD(v___x_1732_);
v_msgData_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1734_, 0, v___x_1731_);
lean_ctor_set(v_msgData_1734_, 1, v___x_1733_);
v___x_1735_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_1734_, v_macroStack_1713_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(lean_object* v_msgData_1740_, lean_object* v_macroStack_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_1740_, v_macroStack_1741_, v___y_1742_);
lean_dec_ref(v___y_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object* v_msg_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_ref_1753_; lean_object* v_macroStack_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1767_; 
v_ref_1753_ = lean_ctor_get(v___y_1750_, 2);
v_macroStack_1754_ = lean_ctor_get(v___y_1746_, 1);
v___x_1755_ = l_Lean_Elab_getBetterRef(v_ref_1753_, v_macroStack_1754_);
v___x_1756_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1745_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
lean_inc(v_macroStack_1754_);
v___x_1758_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_1757_, v_macroStack_1754_, v___y_1750_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1755_);
lean_ctor_set(v___x_1763_, 1, v_a_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 1);
lean_ctor_set(v___x_1761_, 0, v___x_1763_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(lean_object* v_ref_1777_, lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_toCold_1786_; lean_object* v_currRecDepth_1787_; lean_object* v_ref_1788_; uint8_t v_diag_1789_; uint8_t v_suppressElabErrors_1790_; lean_object* v_ref_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_toCold_1786_ = lean_ctor_get(v___y_1783_, 0);
v_currRecDepth_1787_ = lean_ctor_get(v___y_1783_, 1);
v_ref_1788_ = lean_ctor_get(v___y_1783_, 2);
v_diag_1789_ = lean_ctor_get_uint8(v___y_1783_, sizeof(void*)*3);
v_suppressElabErrors_1790_ = lean_ctor_get_uint8(v___y_1783_, sizeof(void*)*3 + 1);
v_ref_1791_ = l_Lean_replaceRef(v_ref_1777_, v_ref_1788_);
lean_inc(v_currRecDepth_1787_);
lean_inc_ref(v_toCold_1786_);
v___x_1792_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1792_, 0, v_toCold_1786_);
lean_ctor_set(v___x_1792_, 1, v_currRecDepth_1787_);
lean_ctor_set(v___x_1792_, 2, v_ref_1791_);
lean_ctor_set_uint8(v___x_1792_, sizeof(void*)*3, v_diag_1789_);
lean_ctor_set_uint8(v___x_1792_, sizeof(void*)*3 + 1, v_suppressElabErrors_1790_);
v___x_1793_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___x_1792_, v___y_1784_);
lean_dec_ref_known(v___x_1792_, 3);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1794_, lean_object* v_msg_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_1794_, v_msg_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v_ref_1794_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v_toCold_1814_; lean_object* v_env_1815_; lean_object* v_currRecDepth_1816_; lean_object* v_ref_1817_; lean_object* v_options_1818_; lean_object* v_maxRecDepth_1819_; lean_object* v_currNamespace_1820_; lean_object* v_openDecls_1821_; lean_object* v_quotContext_1822_; lean_object* v_currMacroScope_1823_; lean_object* v___f_1824_; lean_object* v___f_1825_; lean_object* v___f_1826_; lean_object* v___f_1827_; lean_object* v___f_1828_; lean_object* v_methods_1829_; lean_object* v___x_1830_; lean_object* v_nextMacroScope_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1813_ = lean_st_ref_get(v___y_1811_);
v_toCold_1814_ = lean_ctor_get(v___y_1810_, 0);
v_env_1815_ = lean_ctor_get(v___x_1813_, 0);
lean_inc_ref_n(v_env_1815_, 4);
lean_dec(v___x_1813_);
v_currRecDepth_1816_ = lean_ctor_get(v___y_1810_, 1);
v_ref_1817_ = lean_ctor_get(v___y_1810_, 2);
v_options_1818_ = lean_ctor_get(v_toCold_1814_, 2);
v_maxRecDepth_1819_ = lean_ctor_get(v_toCold_1814_, 3);
v_currNamespace_1820_ = lean_ctor_get(v_toCold_1814_, 4);
v_openDecls_1821_ = lean_ctor_get(v_toCold_1814_, 5);
v_quotContext_1822_ = lean_ctor_get(v_toCold_1814_, 8);
v_currMacroScope_1823_ = lean_ctor_get(v_toCold_1814_, 9);
v___f_1824_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1824_, 0, v_env_1815_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1825_, 0, v_env_1815_);
lean_inc_n(v_openDecls_1821_, 2);
lean_inc_n(v_currNamespace_1820_, 3);
v___f_1826_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1826_, 0, v_env_1815_);
lean_closure_set(v___f_1826_, 1, v_currNamespace_1820_);
lean_closure_set(v___f_1826_, 2, v_openDecls_1821_);
v___f_1827_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1827_, 0, v_currNamespace_1820_);
lean_inc_ref(v_options_1818_);
v___f_1828_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1828_, 0, v_env_1815_);
lean_closure_set(v___f_1828_, 1, v_options_1818_);
lean_closure_set(v___f_1828_, 2, v_currNamespace_1820_);
lean_closure_set(v___f_1828_, 3, v_openDecls_1821_);
v_methods_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1829_, 0, v___f_1824_);
lean_ctor_set(v_methods_1829_, 1, v___f_1827_);
lean_ctor_set(v_methods_1829_, 2, v___f_1825_);
lean_ctor_set(v_methods_1829_, 3, v___f_1826_);
lean_ctor_set(v_methods_1829_, 4, v___f_1828_);
v___x_1830_ = lean_st_ref_get(v___y_1811_);
v_nextMacroScope_1831_ = lean_ctor_get(v___x_1830_, 1);
lean_inc(v_nextMacroScope_1831_);
lean_dec(v___x_1830_);
lean_inc(v_ref_1817_);
lean_inc(v_maxRecDepth_1819_);
lean_inc(v_currRecDepth_1816_);
lean_inc(v_currMacroScope_1823_);
lean_inc(v_quotContext_1822_);
v___x_1832_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1832_, 0, v_methods_1829_);
lean_ctor_set(v___x_1832_, 1, v_quotContext_1822_);
lean_ctor_set(v___x_1832_, 2, v_currMacroScope_1823_);
lean_ctor_set(v___x_1832_, 3, v_currRecDepth_1816_);
lean_ctor_set(v___x_1832_, 4, v_maxRecDepth_1819_);
lean_ctor_set(v___x_1832_, 5, v_ref_1817_);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1834_, 0, v_nextMacroScope_1831_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
lean_ctor_set(v___x_1834_, 2, v___x_1833_);
v___x_1835_ = lean_apply_2(v_x_1805_, v___x_1832_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v_a_1837_; lean_object* v_macroScope_1838_; lean_object* v_traceMsgs_1839_; lean_object* v_expandedMacroDecls_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_a_1836_);
v_a_1837_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1835_, 2);
v_macroScope_1838_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_macroScope_1838_);
v_traceMsgs_1839_ = lean_ctor_get(v_a_1836_, 1);
lean_inc(v_traceMsgs_1839_);
v_expandedMacroDecls_1840_ = lean_ctor_get(v_a_1836_, 2);
lean_inc(v_expandedMacroDecls_1840_);
lean_dec(v_a_1836_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_1840_, v___x_1841_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v_expandedMacroDecls_1840_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; lean_object* v_env_1844_; lean_object* v_ngen_1845_; lean_object* v_auxDeclNGen_1846_; lean_object* v_traceState_1847_; lean_object* v_cache_1848_; lean_object* v_messages_1849_; lean_object* v_infoState_1850_; lean_object* v_snapshotTasks_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref_known(v___x_1842_, 1);
v___x_1843_ = lean_st_ref_take(v___y_1811_);
v_env_1844_ = lean_ctor_get(v___x_1843_, 0);
v_ngen_1845_ = lean_ctor_get(v___x_1843_, 2);
v_auxDeclNGen_1846_ = lean_ctor_get(v___x_1843_, 3);
v_traceState_1847_ = lean_ctor_get(v___x_1843_, 4);
v_cache_1848_ = lean_ctor_get(v___x_1843_, 5);
v_messages_1849_ = lean_ctor_get(v___x_1843_, 6);
v_infoState_1850_ = lean_ctor_get(v___x_1843_, 7);
v_snapshotTasks_1851_ = lean_ctor_get(v___x_1843_, 8);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1843_, 1);
lean_dec(v_unused_1878_);
v___x_1853_ = v___x_1843_;
v_isShared_1854_ = v_isSharedCheck_1877_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snapshotTasks_1851_);
lean_inc(v_infoState_1850_);
lean_inc(v_messages_1849_);
lean_inc(v_cache_1848_);
lean_inc(v_traceState_1847_);
lean_inc(v_auxDeclNGen_1846_);
lean_inc(v_ngen_1845_);
lean_inc(v_env_1844_);
lean_dec(v___x_1843_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1877_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v_macroScope_1838_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_env_1844_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_macroScope_1838_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_ngen_1845_);
lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_auxDeclNGen_1846_);
lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_traceState_1847_);
lean_ctor_set(v_reuseFailAlloc_1876_, 5, v_cache_1848_);
lean_ctor_set(v_reuseFailAlloc_1876_, 6, v_messages_1849_);
lean_ctor_set(v_reuseFailAlloc_1876_, 7, v_infoState_1850_);
lean_ctor_set(v_reuseFailAlloc_1876_, 8, v_snapshotTasks_1851_);
v___x_1856_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_st_ref_put(v___y_1811_, v___x_1856_);
v___x_1858_ = l_List_reverse___redArg(v_traceMsgs_1839_);
v___x_1859_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_1858_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1859_, 0);
lean_dec(v_unused_1867_);
v___x_1861_ = v___x_1859_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_dec(v___x_1859_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_a_1837_);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1837_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_a_1837_);
v_a_1868_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1859_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_traceMsgs_1839_);
lean_dec(v_macroScope_1838_);
lean_dec(v_a_1837_);
v_a_1879_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1842_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1842_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; 
v_a_1887_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1835_, 2);
if (lean_obj_tag(v_a_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_a_1888_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_a_1888_);
v_a_1889_ = lean_ctor_get(v_a_1887_, 1);
lean_inc_ref(v_a_1889_);
lean_dec_ref_known(v_a_1887_, 2);
v___x_1890_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0));
v___x_1891_ = lean_string_dec_eq(v_a_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_a_1889_);
v___x_1893_ = l_Lean_MessageData_ofFormat(v___x_1892_);
v___x_1894_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_1888_, v___x_1893_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v_a_1888_);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; 
lean_dec_ref(v_a_1889_);
v___x_1895_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_1888_);
return v___x_1895_;
}
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(lean_object* v_t_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v_infoState_1910_; uint8_t v_enabled_1911_; 
v___x_1909_ = lean_st_ref_get(v___y_1907_);
v_infoState_1910_ = lean_ctor_get(v___x_1909_, 7);
lean_inc_ref(v_infoState_1910_);
lean_dec(v___x_1909_);
v_enabled_1911_ = lean_ctor_get_uint8(v_infoState_1910_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1910_);
if (v_enabled_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref(v_t_1906_);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; lean_object* v_infoState_1915_; lean_object* v_env_1916_; lean_object* v_nextMacroScope_1917_; lean_object* v_ngen_1918_; lean_object* v_auxDeclNGen_1919_; lean_object* v_traceState_1920_; lean_object* v_cache_1921_; lean_object* v_messages_1922_; lean_object* v_snapshotTasks_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1945_; 
v___x_1914_ = lean_st_ref_take(v___y_1907_);
v_infoState_1915_ = lean_ctor_get(v___x_1914_, 7);
v_env_1916_ = lean_ctor_get(v___x_1914_, 0);
v_nextMacroScope_1917_ = lean_ctor_get(v___x_1914_, 1);
v_ngen_1918_ = lean_ctor_get(v___x_1914_, 2);
v_auxDeclNGen_1919_ = lean_ctor_get(v___x_1914_, 3);
v_traceState_1920_ = lean_ctor_get(v___x_1914_, 4);
v_cache_1921_ = lean_ctor_get(v___x_1914_, 5);
v_messages_1922_ = lean_ctor_get(v___x_1914_, 6);
v_snapshotTasks_1923_ = lean_ctor_get(v___x_1914_, 8);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1925_ = v___x_1914_;
v_isShared_1926_ = v_isSharedCheck_1945_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_snapshotTasks_1923_);
lean_inc(v_infoState_1915_);
lean_inc(v_messages_1922_);
lean_inc(v_cache_1921_);
lean_inc(v_traceState_1920_);
lean_inc(v_auxDeclNGen_1919_);
lean_inc(v_ngen_1918_);
lean_inc(v_nextMacroScope_1917_);
lean_inc(v_env_1916_);
lean_dec(v___x_1914_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1945_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
uint8_t v_enabled_1927_; lean_object* v_assignment_1928_; lean_object* v_lazyAssignment_1929_; lean_object* v_trees_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1944_; 
v_enabled_1927_ = lean_ctor_get_uint8(v_infoState_1915_, sizeof(void*)*3);
v_assignment_1928_ = lean_ctor_get(v_infoState_1915_, 0);
v_lazyAssignment_1929_ = lean_ctor_get(v_infoState_1915_, 1);
v_trees_1930_ = lean_ctor_get(v_infoState_1915_, 2);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_infoState_1915_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1932_ = v_infoState_1915_;
v_isShared_1933_ = v_isSharedCheck_1944_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_trees_1930_);
lean_inc(v_lazyAssignment_1929_);
lean_inc(v_assignment_1928_);
lean_dec(v_infoState_1915_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1944_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1934_ = lean_box(0);
v___x_1935_ = l_Lean_PersistentArray_push___redArg(v_trees_1930_, v_t_1906_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 2, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_assignment_1928_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_lazyAssignment_1929_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v___x_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*3, v_enabled_1927_);
v___x_1937_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1939_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 7, v___x_1937_);
v___x_1939_ = v___x_1925_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_env_1916_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_nextMacroScope_1917_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_ngen_1918_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_auxDeclNGen_1919_);
lean_ctor_set(v_reuseFailAlloc_1942_, 4, v_traceState_1920_);
lean_ctor_set(v_reuseFailAlloc_1942_, 5, v_cache_1921_);
lean_ctor_set(v_reuseFailAlloc_1942_, 6, v_messages_1922_);
lean_ctor_set(v_reuseFailAlloc_1942_, 7, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1942_, 8, v_snapshotTasks_1923_);
v___x_1939_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_st_ref_put(v___y_1907_, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1934_);
return v___x_1941_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(lean_object* v_t_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_1946_, v___y_1947_);
lean_dec(v___y_1947_);
return v_res_1949_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_unsigned_to_nat(32u);
v___x_1951_ = lean_mk_empty_array_with_capacity(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1(void){
_start:
{
size_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1953_ = ((size_t)5ULL);
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_unsigned_to_nat(32u);
v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1955_);
v___x_1957_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
v___x_1958_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v___x_1956_);
lean_ctor_set(v___x_1958_, 2, v___x_1954_);
lean_ctor_set(v___x_1958_, 3, v___x_1954_);
lean_ctor_set_usize(v___x_1958_, 4, v___x_1953_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object* v_t_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v_infoState_1968_; uint8_t v_enabled_1969_; 
v___x_1967_ = lean_st_ref_get(v___y_1965_);
v_infoState_1968_ = lean_ctor_get(v___x_1967_, 7);
lean_inc_ref(v_infoState_1968_);
lean_dec(v___x_1967_);
v_enabled_1969_ = lean_ctor_get_uint8(v_infoState_1968_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1968_);
if (v_enabled_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_t_1959_);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_t_1959_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_1973_, v___y_1965_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object* v_t_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v_t_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object* v_info_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_info_1984_);
v___x_1993_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_1992_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object* v_info_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2002_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_2010_, uint8_t v___y_2011_, lean_object* v_x_2012_){
_start:
{
if (lean_obj_tag(v_x_2012_) == 1)
{
lean_object* v_pre_2013_; 
v_pre_2013_ = lean_ctor_get(v_x_2012_, 0);
switch(lean_obj_tag(v_pre_2013_))
{
case 1:
{
lean_object* v_pre_2014_; 
v_pre_2014_ = lean_ctor_get(v_pre_2013_, 0);
switch(lean_obj_tag(v_pre_2014_))
{
case 0:
{
lean_object* v_str_2015_; lean_object* v_str_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_str_2015_ = lean_ctor_get(v_x_2012_, 1);
v_str_2016_ = lean_ctor_get(v_pre_2013_, 1);
v___x_2017_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0));
v___x_2018_ = lean_string_dec_eq(v_str_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1));
v___x_2020_ = lean_string_dec_eq(v_str_2016_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2));
v___x_2022_ = lean_string_dec_eq(v_str_2015_, v___x_2021_);
if (v___x_2022_ == 0)
{
return v___x_2022_;
}
else
{
return v_suppressElabErrors_2010_;
}
}
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3));
v___x_2024_ = lean_string_dec_eq(v_str_2015_, v___x_2023_);
if (v___x_2024_ == 0)
{
return v___x_2024_;
}
else
{
return v_suppressElabErrors_2010_;
}
}
}
case 1:
{
lean_object* v_pre_2025_; 
v_pre_2025_ = lean_ctor_get(v_pre_2014_, 0);
if (lean_obj_tag(v_pre_2025_) == 0)
{
lean_object* v_str_2026_; lean_object* v_str_2027_; lean_object* v_str_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_str_2026_ = lean_ctor_get(v_x_2012_, 1);
v_str_2027_ = lean_ctor_get(v_pre_2013_, 1);
v_str_2028_ = lean_ctor_get(v_pre_2014_, 1);
v___x_2029_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4));
v___x_2030_ = lean_string_dec_eq(v_str_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5));
v___x_2032_ = lean_string_dec_eq(v_str_2027_, v___x_2031_);
if (v___x_2032_ == 0)
{
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6));
v___x_2034_ = lean_string_dec_eq(v_str_2026_, v___x_2033_);
if (v___x_2034_ == 0)
{
return v___x_2034_;
}
else
{
return v_suppressElabErrors_2010_;
}
}
}
}
else
{
return v___y_2011_;
}
}
default: 
{
return v___y_2011_;
}
}
}
case 0:
{
lean_object* v_str_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_str_2035_ = lean_ctor_get(v_x_2012_, 1);
v___x_2036_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0));
v___x_2037_ = lean_string_dec_eq(v_str_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
return v___x_2037_;
}
else
{
return v_suppressElabErrors_2010_;
}
}
default: 
{
return v___y_2011_;
}
}
}
else
{
return v___y_2011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2038_, lean_object* v___y_2039_, lean_object* v_x_2040_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2041_; uint8_t v___y_21499__boxed_2042_; uint8_t v_res_2043_; lean_object* v_r_2044_; 
v_suppressElabErrors_boxed_2041_ = lean_unbox(v_suppressElabErrors_2038_);
v___y_21499__boxed_2042_ = lean_unbox(v___y_2039_);
v_res_2043_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_2041_, v___y_21499__boxed_2042_, v_x_2040_);
lean_dec(v_x_2040_);
v_r_2044_ = lean_box(v_res_2043_);
return v_r_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(lean_object* v_ref_2045_, lean_object* v_msgData_2046_, uint8_t v_severity_2047_, uint8_t v_isSilent_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
uint8_t v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v_currNamespace_2062_; lean_object* v_openDecls_2063_; lean_object* v___y_2064_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___y_2095_; uint8_t v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; uint8_t v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; uint8_t v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; uint8_t v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; uint8_t v___y_2138_; uint8_t v___x_2143_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; uint8_t v___y_2150_; uint8_t v___y_2151_; lean_object* v___y_2152_; uint8_t v___y_2153_; uint8_t v___y_2155_; uint8_t v___x_2173_; 
v___x_2143_ = 2;
v___x_2173_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2047_, v___x_2143_);
if (v___x_2173_ == 0)
{
v___y_2155_ = v___x_2173_;
goto v___jp_2154_;
}
else
{
uint8_t v___x_2174_; 
lean_inc_ref(v_msgData_2046_);
v___x_2174_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2046_);
v___y_2155_ = v___x_2174_;
goto v___jp_2154_;
}
v___jp_2054_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_env_2069_; lean_object* v_nextMacroScope_2070_; lean_object* v_ngen_2071_; lean_object* v_auxDeclNGen_2072_; lean_object* v_traceState_2073_; lean_object* v_cache_2074_; lean_object* v_messages_2075_; lean_object* v_infoState_2076_; lean_object* v_snapshotTasks_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2088_; 
lean_inc(v_openDecls_2063_);
lean_inc(v_currNamespace_2062_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_currNamespace_2062_);
lean_ctor_set(v___x_2065_, 1, v_openDecls_2063_);
v___x_2066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___y_2057_);
lean_inc_ref(v___y_2060_);
lean_inc_ref(v___y_2056_);
v___x_2067_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2067_, 0, v___y_2056_);
lean_ctor_set(v___x_2067_, 1, v___y_2059_);
lean_ctor_set(v___x_2067_, 2, v___y_2061_);
lean_ctor_set(v___x_2067_, 3, v___y_2060_);
lean_ctor_set(v___x_2067_, 4, v___x_2066_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5, v___y_2058_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 1, v___y_2055_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 2, v_isSilent_2048_);
v___x_2068_ = lean_st_ref_take(v___y_2064_);
v_env_2069_ = lean_ctor_get(v___x_2068_, 0);
v_nextMacroScope_2070_ = lean_ctor_get(v___x_2068_, 1);
v_ngen_2071_ = lean_ctor_get(v___x_2068_, 2);
v_auxDeclNGen_2072_ = lean_ctor_get(v___x_2068_, 3);
v_traceState_2073_ = lean_ctor_get(v___x_2068_, 4);
v_cache_2074_ = lean_ctor_get(v___x_2068_, 5);
v_messages_2075_ = lean_ctor_get(v___x_2068_, 6);
v_infoState_2076_ = lean_ctor_get(v___x_2068_, 7);
v_snapshotTasks_2077_ = lean_ctor_get(v___x_2068_, 8);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2079_ = v___x_2068_;
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snapshotTasks_2077_);
lean_inc(v_infoState_2076_);
lean_inc(v_messages_2075_);
lean_inc(v_cache_2074_);
lean_inc(v_traceState_2073_);
lean_inc(v_auxDeclNGen_2072_);
lean_inc(v_ngen_2071_);
lean_inc(v_nextMacroScope_2070_);
lean_inc(v_env_2069_);
lean_dec(v___x_2068_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = l_Lean_MessageLog_add(v___x_2067_, v_messages_2075_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 6, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_env_2069_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_nextMacroScope_2070_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_ngen_2071_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_auxDeclNGen_2072_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_traceState_2073_);
lean_ctor_set(v_reuseFailAlloc_2087_, 5, v_cache_2074_);
lean_ctor_set(v_reuseFailAlloc_2087_, 6, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2087_, 7, v_infoState_2076_);
lean_ctor_set(v_reuseFailAlloc_2087_, 8, v_snapshotTasks_2077_);
v___x_2084_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_st_ref_put(v___y_2064_, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2081_);
return v___x_2086_;
}
}
}
v___jp_2089_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2115_; 
v___x_2100_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2046_);
v___x_2101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_2100_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2115_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2115_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_inc_ref_n(v___y_2093_, 2);
v___x_2106_ = l_Lean_FileMap_toPosition(v___y_2093_, v___y_2098_);
lean_dec(v___y_2098_);
v___x_2107_ = l_Lean_FileMap_toPosition(v___y_2093_, v___y_2099_);
lean_dec(v___y_2099_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
v___x_2109_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
if (v___y_2096_ == 0)
{
lean_del_object(v___x_2104_);
lean_dec_ref(v___y_2092_);
v___y_2055_ = v___y_2095_;
v___y_2056_ = v___y_2094_;
v___y_2057_ = v_a_2102_;
v___y_2058_ = v___y_2097_;
v___y_2059_ = v___x_2106_;
v___y_2060_ = v___x_2109_;
v___y_2061_ = v___x_2108_;
v_currNamespace_2062_ = v___y_2090_;
v_openDecls_2063_ = v___y_2091_;
v___y_2064_ = v___y_2052_;
goto v___jp_2054_;
}
else
{
uint8_t v___x_2110_; 
lean_inc(v_a_2102_);
v___x_2110_ = l_Lean_MessageData_hasTag(v___y_2092_, v_a_2102_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec_ref_known(v___x_2108_, 1);
lean_dec_ref(v___x_2106_);
lean_dec(v_a_2102_);
v___x_2111_ = lean_box(0);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2111_);
v___x_2113_ = v___x_2104_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
else
{
lean_del_object(v___x_2104_);
v___y_2055_ = v___y_2095_;
v___y_2056_ = v___y_2094_;
v___y_2057_ = v_a_2102_;
v___y_2058_ = v___y_2097_;
v___y_2059_ = v___x_2106_;
v___y_2060_ = v___x_2109_;
v___y_2061_ = v___x_2108_;
v_currNamespace_2062_ = v___y_2090_;
v_openDecls_2063_ = v___y_2091_;
v___y_2064_ = v___y_2052_;
goto v___jp_2054_;
}
}
}
}
v___jp_2116_:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_Syntax_getTailPos_x3f(v___y_2125_, v___y_2123_);
lean_dec(v___y_2125_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_inc(v___y_2126_);
v___y_2090_ = v___y_2117_;
v___y_2091_ = v___y_2118_;
v___y_2092_ = v___y_2119_;
v___y_2093_ = v___y_2120_;
v___y_2094_ = v___y_2122_;
v___y_2095_ = v___y_2121_;
v___y_2096_ = v___y_2124_;
v___y_2097_ = v___y_2123_;
v___y_2098_ = v___y_2126_;
v___y_2099_ = v___y_2126_;
goto v___jp_2089_;
}
else
{
lean_object* v_val_2128_; 
v_val_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___y_2090_ = v___y_2117_;
v___y_2091_ = v___y_2118_;
v___y_2092_ = v___y_2119_;
v___y_2093_ = v___y_2120_;
v___y_2094_ = v___y_2122_;
v___y_2095_ = v___y_2121_;
v___y_2096_ = v___y_2124_;
v___y_2097_ = v___y_2123_;
v___y_2098_ = v___y_2126_;
v___y_2099_ = v_val_2128_;
goto v___jp_2089_;
}
}
v___jp_2129_:
{
lean_object* v_ref_2139_; lean_object* v___x_2140_; 
v_ref_2139_ = l_Lean_replaceRef(v_ref_2045_, v___y_2137_);
v___x_2140_ = l_Lean_Syntax_getPos_x3f(v_ref_2139_, v___y_2136_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___y_2117_ = v___y_2130_;
v___y_2118_ = v___y_2131_;
v___y_2119_ = v___y_2132_;
v___y_2120_ = v___y_2133_;
v___y_2121_ = v___y_2138_;
v___y_2122_ = v___y_2134_;
v___y_2123_ = v___y_2136_;
v___y_2124_ = v___y_2135_;
v___y_2125_ = v_ref_2139_;
v___y_2126_ = v___x_2141_;
goto v___jp_2116_;
}
else
{
lean_object* v_val_2142_; 
v_val_2142_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_val_2142_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_2117_ = v___y_2130_;
v___y_2118_ = v___y_2131_;
v___y_2119_ = v___y_2132_;
v___y_2120_ = v___y_2133_;
v___y_2121_ = v___y_2138_;
v___y_2122_ = v___y_2134_;
v___y_2123_ = v___y_2136_;
v___y_2124_ = v___y_2135_;
v___y_2125_ = v_ref_2139_;
v___y_2126_ = v_val_2142_;
goto v___jp_2116_;
}
}
v___jp_2144_:
{
if (v___y_2153_ == 0)
{
v___y_2130_ = v___y_2147_;
v___y_2131_ = v___y_2148_;
v___y_2132_ = v___y_2149_;
v___y_2133_ = v___y_2145_;
v___y_2134_ = v___y_2146_;
v___y_2135_ = v___y_2151_;
v___y_2136_ = v___y_2150_;
v___y_2137_ = v___y_2152_;
v___y_2138_ = v_severity_2047_;
goto v___jp_2129_;
}
else
{
v___y_2130_ = v___y_2147_;
v___y_2131_ = v___y_2148_;
v___y_2132_ = v___y_2149_;
v___y_2133_ = v___y_2145_;
v___y_2134_ = v___y_2146_;
v___y_2135_ = v___y_2151_;
v___y_2136_ = v___y_2150_;
v___y_2137_ = v___y_2152_;
v___y_2138_ = v___x_2143_;
goto v___jp_2129_;
}
}
v___jp_2154_:
{
if (v___y_2155_ == 0)
{
lean_object* v_toCold_2156_; lean_object* v_ref_2157_; uint8_t v_suppressElabErrors_2158_; lean_object* v_fileName_2159_; lean_object* v_fileMap_2160_; lean_object* v_options_2161_; lean_object* v_currNamespace_2162_; lean_object* v_openDecls_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___f_2166_; uint8_t v___x_2167_; uint8_t v___x_2168_; 
v_toCold_2156_ = lean_ctor_get(v___y_2051_, 0);
v_ref_2157_ = lean_ctor_get(v___y_2051_, 2);
v_suppressElabErrors_2158_ = lean_ctor_get_uint8(v___y_2051_, sizeof(void*)*3 + 1);
v_fileName_2159_ = lean_ctor_get(v_toCold_2156_, 0);
v_fileMap_2160_ = lean_ctor_get(v_toCold_2156_, 1);
v_options_2161_ = lean_ctor_get(v_toCold_2156_, 2);
v_currNamespace_2162_ = lean_ctor_get(v_toCold_2156_, 4);
v_openDecls_2163_ = lean_ctor_get(v_toCold_2156_, 5);
v___x_2164_ = lean_box(v_suppressElabErrors_2158_);
v___x_2165_ = lean_box(v___y_2155_);
v___f_2166_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2166_, 0, v___x_2164_);
lean_closure_set(v___f_2166_, 1, v___x_2165_);
v___x_2167_ = 1;
v___x_2168_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2047_, v___x_2167_);
if (v___x_2168_ == 0)
{
v___y_2145_ = v_fileMap_2160_;
v___y_2146_ = v_fileName_2159_;
v___y_2147_ = v_currNamespace_2162_;
v___y_2148_ = v_openDecls_2163_;
v___y_2149_ = v___f_2166_;
v___y_2150_ = v___y_2155_;
v___y_2151_ = v_suppressElabErrors_2158_;
v___y_2152_ = v_ref_2157_;
v___y_2153_ = v___x_2168_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = l_Lean_warningAsError;
v___x_2170_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_2161_, v___x_2169_);
v___y_2145_ = v_fileMap_2160_;
v___y_2146_ = v_fileName_2159_;
v___y_2147_ = v_currNamespace_2162_;
v___y_2148_ = v_openDecls_2163_;
v___y_2149_ = v___f_2166_;
v___y_2150_ = v___y_2155_;
v___y_2151_ = v_suppressElabErrors_2158_;
v___y_2152_ = v_ref_2157_;
v___y_2153_ = v___x_2170_;
goto v___jp_2144_;
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v_msgData_2046_);
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(lean_object* v_ref_2175_, lean_object* v_msgData_2176_, lean_object* v_severity_2177_, lean_object* v_isSilent_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v_severity_boxed_2184_; uint8_t v_isSilent_boxed_2185_; lean_object* v_res_2186_; 
v_severity_boxed_2184_ = lean_unbox(v_severity_2177_);
v_isSilent_boxed_2185_ = lean_unbox(v_isSilent_2178_);
v_res_2186_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2175_, v_msgData_2176_, v_severity_boxed_2184_, v_isSilent_boxed_2185_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v_ref_2175_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object* v_ref_2187_, lean_object* v_msgData_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = 2;
v___x_2197_ = 0;
v___x_2198_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2187_, v_msgData_2188_, v___x_2196_, v___x_2197_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object* v_ref_2199_, lean_object* v_msgData_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v_ref_2199_, v_msgData_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_ref_2199_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object* v_ref_2209_, lean_object* v_msgData_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = 1;
v___x_2219_ = 0;
v___x_2220_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2209_, v_msgData_2210_, v___x_2218_, v___x_2219_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object* v_ref_2221_, lean_object* v_msgData_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v_ref_2221_, v_msgData_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v_ref_2221_);
return v_res_2230_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* v_stx_2258_, lean_object* v_expType_x3f_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
uint8_t v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2288_; lean_object* v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v_fst_2360_; lean_object* v_snd_2361_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; uint8_t v___y_2389_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_inc(v_stx_2258_);
v___x_2407_ = l_Lean_Syntax_getKind(v_stx_2258_);
v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_2406_, v___x_2407_);
lean_dec(v___x_2407_);
if (lean_obj_tag(v___x_2408_) == 1)
{
lean_object* v_val_2409_; lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2442_; 
v_val_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v_fst_2410_ = lean_ctor_get(v_val_2409_, 0);
v_snd_2411_ = lean_ctor_get(v_val_2409_, 1);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_val_2409_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2413_ = v_val_2409_;
v_isShared_2414_ = v_isSharedCheck_2442_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_snd_2411_);
lean_inc(v_fst_2410_);
lean_dec(v_val_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2442_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v_env_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; 
v___x_2415_ = lean_st_ref_get(v_a_2265_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_env_2416_);
lean_dec(v___x_2415_);
v___x_2417_ = 1;
lean_inc(v_snd_2411_);
v___x_2418_ = l_Lean_Environment_contains(v_env_2416_, v_snd_2411_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
lean_dec(v_expType_x3f_2259_);
lean_dec(v_stx_2258_);
v___x_2419_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
v___x_2420_ = l_Lean_MessageData_ofName(v_snd_2411_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 7);
lean_ctor_set(v___x_2413_, 1, v___x_2420_);
lean_ctor_set(v___x_2413_, 0, v___x_2419_);
v___x_2422_ = v___x_2413_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v___x_2423_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
v___x_2426_ = l_Lean_MessageData_ofName(v_fst_2410_);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = l_Lean_MessageData_hint_x27(v___x_2429_);
v___x_2431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2424_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_2431_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_del_object(v___x_2413_);
lean_dec(v_snd_2411_);
lean_dec(v_fst_2410_);
v___y_2396_ = v_a_2260_;
v___y_2397_ = v_a_2261_;
v___y_2398_ = v_a_2262_;
v___y_2399_ = v_a_2263_;
v___y_2400_ = v_a_2264_;
v___y_2401_ = v_a_2265_;
goto v___jp_2395_;
}
}
}
else
{
lean_dec(v___x_2408_);
v___y_2396_ = v_a_2260_;
v___y_2397_ = v_a_2261_;
v___y_2398_ = v_a_2262_;
v___y_2399_ = v_a_2263_;
v___y_2400_ = v_a_2264_;
v___y_2401_ = v_a_2265_;
goto v___jp_2395_;
}
v___jp_2267_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed), 3, 1);
lean_closure_set(v___x_2275_, 0, v_stx_2258_);
v___x_2276_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_2275_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l_Lean_Elab_Term_elabTerm(v_a_2277_, v_expType_x3f_2259_, v___y_2268_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2278_;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_expType_x3f_2259_);
v_a_2279_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2276_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2276_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
v___jp_2287_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_partialId_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2351_; 
v___x_2297_ = l_Lean_Syntax_getNumArgs(v___y_2296_);
v___x_2298_ = lean_unsigned_to_nat(2u);
v___x_2299_ = lean_nat_sub(v___x_2297_, v___x_2298_);
lean_dec(v___x_2297_);
v_partialId_2300_ = l_Lean_Syntax_getArg(v___y_2296_, v___x_2299_);
lean_dec(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2296_);
lean_ctor_set(v___x_2301_, 1, v_partialId_2300_);
v___x_2302_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_2301_, v___y_2293_, v___y_2288_, v___y_2292_, v___y_2295_, v___y_2289_, v___y_2291_);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v___x_2302_, 0);
lean_dec(v_unused_2352_);
v___x_2304_ = v___x_2302_;
v_isShared_2305_ = v_isSharedCheck_2351_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v___x_2302_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2351_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2306_ = l_Lean_Syntax_getId(v___y_2294_);
v___x_2307_ = l_Lean_Name_eraseMacroScopes(v___x_2306_);
lean_dec(v___x_2306_);
lean_inc(v___x_2307_);
lean_inc(v___y_2294_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___y_2294_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 6);
lean_ctor_set(v___x_2304_, 0, v___x_2308_);
v___x_2310_ = v___x_2304_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; 
v___x_2311_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2310_, v___y_2293_, v___y_2288_, v___y_2292_, v___y_2295_, v___y_2289_, v___y_2291_);
lean_dec_ref(v___x_2311_);
v___x_2312_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_2307_, v___y_2291_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
if (lean_obj_tag(v_a_2313_) == 1)
{
lean_object* v_val_2314_; lean_object* v_metadata_2315_; lean_object* v_removedVersion_x3f_2316_; 
v_val_2314_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v_a_2313_, 1);
v_metadata_2315_ = lean_ctor_get(v_val_2314_, 1);
lean_inc_ref(v_metadata_2315_);
lean_dec(v_val_2314_);
v_removedVersion_x3f_2316_ = lean_ctor_get(v_metadata_2315_, 2);
lean_inc(v_removedVersion_x3f_2316_);
lean_dec_ref(v_metadata_2315_);
if (lean_obj_tag(v_removedVersion_x3f_2316_) == 1)
{
lean_object* v_val_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_val_2317_ = lean_ctor_get(v_removedVersion_x3f_2316_, 0);
lean_inc(v_val_2317_);
lean_dec_ref_known(v_removedVersion_x3f_2316_, 1);
v___x_2318_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
v___x_2319_ = l_Lean_MessageData_ofName(v___x_2307_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_stringToMessageData(v_val_2317_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_2294_, v___x_2326_, v___y_2293_, v___y_2288_, v___y_2292_, v___y_2295_, v___y_2289_, v___y_2291_);
lean_dec(v___y_2294_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_dec_ref_known(v___x_2327_, 1);
v___y_2268_ = v___y_2290_;
v___y_2269_ = v___y_2293_;
v___y_2270_ = v___y_2288_;
v___y_2271_ = v___y_2292_;
v___y_2272_ = v___y_2295_;
v___y_2273_ = v___y_2289_;
v___y_2274_ = v___y_2291_;
goto v___jp_2267_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_expType_x3f_2259_);
lean_dec(v_stx_2258_);
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
else
{
lean_dec(v_removedVersion_x3f_2316_);
lean_dec(v___x_2307_);
lean_dec(v___y_2294_);
v___y_2268_ = v___y_2290_;
v___y_2269_ = v___y_2293_;
v___y_2270_ = v___y_2288_;
v___y_2271_ = v___y_2292_;
v___y_2272_ = v___y_2295_;
v___y_2273_ = v___y_2289_;
v___y_2274_ = v___y_2291_;
goto v___jp_2267_;
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_a_2313_);
v___x_2336_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
v___x_2337_ = l_Lean_MessageData_ofName(v___x_2307_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_2294_, v___x_2340_, v___y_2293_, v___y_2288_, v___y_2292_, v___y_2295_, v___y_2289_, v___y_2291_);
lean_dec(v___y_2294_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_dec_ref_known(v___x_2341_, 1);
v___y_2268_ = v___y_2290_;
v___y_2269_ = v___y_2293_;
v___y_2270_ = v___y_2288_;
v___y_2271_ = v___y_2292_;
v___y_2272_ = v___y_2295_;
v___y_2273_ = v___y_2289_;
v___y_2274_ = v___y_2291_;
goto v___jp_2267_;
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_expType_x3f_2259_);
lean_dec(v_stx_2258_);
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
v___jp_2353_:
{
lean_object* v___x_2362_; uint8_t v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = l_Lean_Syntax_getNumArgs(v_stx_2258_);
v___x_2363_ = lean_nat_dec_eq(v___x_2362_, v_snd_2361_);
v___x_2364_ = 1;
if (v___x_2363_ == 0)
{
lean_dec(v___x_2362_);
lean_inc(v_stx_2258_);
v___y_2288_ = v___y_2354_;
v___y_2289_ = v___y_2355_;
v___y_2290_ = v___x_2364_;
v___y_2291_ = v___y_2358_;
v___y_2292_ = v___y_2357_;
v___y_2293_ = v___y_2356_;
v___y_2294_ = v_fst_2360_;
v___y_2295_ = v___y_2359_;
v___y_2296_ = v_stx_2258_;
goto v___jp_2287_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2365_ = l_Lean_Syntax_getArgs(v_stx_2258_);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_sub(v___x_2362_, v___x_2366_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = l_Array_toSubarray___redArg(v___x_2365_, v___x_2368_, v___x_2367_);
v___x_2370_ = l_Subarray_copy___redArg(v___x_2369_);
lean_inc(v_stx_2258_);
v___x_2371_ = l_Lean_Syntax_setArgs(v_stx_2258_, v___x_2370_);
v___y_2288_ = v___y_2354_;
v___y_2289_ = v___y_2355_;
v___y_2290_ = v___x_2364_;
v___y_2291_ = v___y_2358_;
v___y_2292_ = v___y_2357_;
v___y_2293_ = v___y_2356_;
v___y_2294_ = v_fst_2360_;
v___y_2295_ = v___y_2359_;
v___y_2296_ = v___x_2371_;
goto v___jp_2287_;
}
}
v___jp_2372_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = lean_unsigned_to_nat(2u);
v___x_2380_ = l_Lean_Syntax_getArg(v_stx_2258_, v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(5u);
v___y_2354_ = v___y_2373_;
v___y_2355_ = v___y_2374_;
v___y_2356_ = v___y_2377_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___y_2375_;
v___y_2359_ = v___y_2378_;
v_fst_2360_ = v___x_2380_;
v_snd_2361_ = v___x_2381_;
goto v___jp_2353_;
}
v___jp_2382_:
{
if (v___y_2389_ == 0)
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_stx_2258_);
v___x_2391_ = l_Lean_Syntax_isOfKind(v_stx_2258_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = l_Lean_Syntax_getArg(v_stx_2258_, v___x_2392_);
v___x_2394_ = lean_unsigned_to_nat(4u);
v___y_2354_ = v___y_2383_;
v___y_2355_ = v___y_2384_;
v___y_2356_ = v___y_2387_;
v___y_2357_ = v___y_2386_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v___y_2388_;
v_fst_2360_ = v___x_2393_;
v_snd_2361_ = v___x_2394_;
goto v___jp_2353_;
}
else
{
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2384_;
v___y_2375_ = v___y_2385_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2387_;
v___y_2378_ = v___y_2388_;
goto v___jp_2372_;
}
}
else
{
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2384_;
v___y_2375_ = v___y_2385_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2387_;
v___y_2378_ = v___y_2388_;
goto v___jp_2372_;
}
}
v___jp_2395_:
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_stx_2258_);
v___x_2403_ = l_Lean_Syntax_isOfKind(v_stx_2258_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_stx_2258_);
v___x_2405_ = l_Lean_Syntax_isOfKind(v_stx_2258_, v___x_2404_);
v___y_2383_ = v___y_2397_;
v___y_2384_ = v___y_2400_;
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2398_;
v___y_2387_ = v___y_2396_;
v___y_2388_ = v___y_2399_;
v___y_2389_ = v___x_2405_;
goto v___jp_2382_;
}
else
{
v___y_2383_ = v___y_2397_;
v___y_2384_ = v___y_2400_;
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2398_;
v___y_2387_ = v___y_2396_;
v___y_2388_ = v___y_2399_;
v___y_2389_ = v___x_2403_;
goto v___jp_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object* v_stx_2443_, lean_object* v_expType_x3f_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(v_stx_2443_, v_expType_x3f_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object* v_00_u03b1_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_2454_, v___y_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_x_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_2458_, v_x_2459_, v___y_2460_, v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v_x_2459_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object* v_00_u03b1_2463_, lean_object* v_ref_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_2464_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2473_, lean_object* v_ref_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_2473_, v_ref_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object* v_00_u03b1_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* v_00_u03b1_2501_, lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* v_00_u03b1_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(v_00_u03b1_2511_, v_x_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(lean_object* v_t_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_2521_, v___y_2527_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(lean_object* v_t_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object* v_00_u03b2_2539_, lean_object* v_m_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_2540_, v_a_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object* v_00_u03b2_2543_, lean_object* v_m_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_2543_, v_m_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_m_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object* v_00_u03b1_2547_, lean_object* v_msg_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_msg_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(v_00_u03b1_2557_, v_msg_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object* v_cls_2567_, lean_object* v_msg_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_2567_, v_msg_2568_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object* v_cls_2577_, lean_object* v_msg_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_2577_, v_msg_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object* v_as_2587_, lean_object* v_as_x27_2588_, lean_object* v_b_2589_, lean_object* v_a_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_2588_, v_b_2589_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object* v_as_2599_, lean_object* v_as_x27_2600_, lean_object* v_b_2601_, lean_object* v_a_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_2599_, v_as_x27_2600_, v_b_2601_, v_a_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v_as_x27_2600_);
lean_dec(v_as_2599_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object* v_00_u03b1_2611_, lean_object* v_ref_2612_, lean_object* v_msg_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_2612_, v_msg_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_ref_2623_, lean_object* v_msg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_2622_, v_ref_2623_, v_msg_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v_ref_2623_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(lean_object* v_ref_2633_, lean_object* v_msgData_2634_, uint8_t v_severity_2635_, uint8_t v_isSilent_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2633_, v_msgData_2634_, v_severity_2635_, v_isSilent_2636_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(lean_object* v_ref_2645_, lean_object* v_msgData_2646_, lean_object* v_severity_2647_, lean_object* v_isSilent_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v_severity_boxed_2656_; uint8_t v_isSilent_boxed_2657_; lean_object* v_res_2658_; 
v_severity_boxed_2656_ = lean_unbox(v_severity_2647_);
v_isSilent_boxed_2657_ = lean_unbox(v_isSilent_2648_);
v_res_2658_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_2645_, v_msgData_2646_, v_severity_boxed_2656_, v_isSilent_boxed_2657_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v_ref_2645_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(lean_object* v_00_u03b2_2659_, lean_object* v_a_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_2660_, v_x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(lean_object* v_00_u03b2_2663_, lean_object* v_a_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_2663_, v_a_2664_, v_x_2665_);
lean_dec(v_x_2665_);
lean_dec(v_a_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object* v_msgData_2667_, lean_object* v_macroStack_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_2667_, v_macroStack_2668_, v___y_2673_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object* v_msgData_2677_, lean_object* v_macroStack_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_2677_, v_macroStack_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(lean_object* v_00_u03b2_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
uint8_t v___x_2690_; 
v___x_2690_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_2688_, v_x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(lean_object* v_00_u03b2_2691_, lean_object* v_x_2692_, lean_object* v_x_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_2691_, v_x_2692_, v_x_2693_);
lean_dec_ref(v_x_2693_);
lean_dec_ref(v_x_2692_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(lean_object* v_00_u03b2_2696_, lean_object* v_x_2697_, size_t v_x_2698_, lean_object* v_x_2699_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_2697_, v_x_2698_, v_x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(lean_object* v_00_u03b2_2701_, lean_object* v_x_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
size_t v_x_22569__boxed_2705_; uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_x_22569__boxed_2705_ = lean_unbox_usize(v_x_2703_);
lean_dec(v_x_2703_);
v_res_2706_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_2701_, v_x_2702_, v_x_22569__boxed_2705_, v_x_2704_);
lean_dec_ref(v_x_2704_);
lean_dec_ref(v_x_2702_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(lean_object* v_00_u03b2_2708_, lean_object* v_keys_2709_, lean_object* v_vals_2710_, lean_object* v_heq_2711_, lean_object* v_i_2712_, lean_object* v_k_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_2709_, v_i_2712_, v_k_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(lean_object* v_00_u03b2_2715_, lean_object* v_keys_2716_, lean_object* v_vals_2717_, lean_object* v_heq_2718_, lean_object* v_i_2719_, lean_object* v_k_2720_){
_start:
{
uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_res_2721_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_2715_, v_keys_2716_, v_vals_2717_, v_heq_2718_, v_i_2719_, v_k_2720_);
lean_dec_ref(v_k_2720_);
lean_dec_ref(v_vals_2717_);
lean_dec_ref(v_keys_2716_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2731_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2732_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
v___x_2733_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2734_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2735_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2731_, v___x_2732_, v___x_2733_, v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2739_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2740_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
v___x_2741_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2742_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2743_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2739_, v___x_2740_, v___x_2741_, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2747_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2748_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2750_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2751_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2747_, v___x_2748_, v___x_2749_, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2755_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2756_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
v___x_2757_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2758_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2759_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2755_, v___x_2756_, v___x_2757_, v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2763_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2764_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
v___x_2765_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2766_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2767_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2763_, v___x_2764_, v___x_2765_, v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2771_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2772_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
v___x_2773_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2774_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2775_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2771_, v___x_2772_, v___x_2773_, v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
return v_res_2777_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___f_2779_; 
v___x_2778_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2779_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2779_, 0, v___x_2778_);
return v___f_2779_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___f_2781_; 
v___x_2780_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2781_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2781_, 0, v___x_2780_);
return v___f_2781_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2(void){
_start:
{
lean_object* v___f_2782_; lean_object* v___f_2783_; lean_object* v___x_2784_; 
v___f_2782_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1);
v___f_2783_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___f_2783_);
lean_ctor_set(v___x_2784_, 1, v___f_2782_);
return v___x_2784_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___f_2786_; 
v___x_2785_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2);
v___f_2786_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2786_, 0, v___x_2785_);
return v___f_2786_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___f_2788_; 
v___x_2787_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2);
v___f_2788_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2788_, 0, v___x_2787_);
return v___f_2788_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5(void){
_start:
{
lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; 
v___f_2789_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4);
v___f_2790_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___f_2790_);
lean_ctor_set(v___x_2791_, 1, v___f_2789_);
return v___x_2791_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___f_2793_; 
v___x_2792_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5);
v___f_2793_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2793_, 0, v___x_2792_);
return v___f_2793_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___f_2795_; 
v___x_2794_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5);
v___f_2795_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2795_, 0, v___x_2794_);
return v___f_2795_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8(void){
_start:
{
lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; 
v___f_2796_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7);
v___f_2797_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6);
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___f_2797_);
lean_ctor_set(v___x_2798_, 1, v___f_2796_);
return v___x_2798_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___f_2800_; 
v___x_2799_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8);
v___f_2800_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2800_, 0, v___x_2799_);
return v___f_2800_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___f_2802_; 
v___x_2801_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8);
v___f_2802_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2802_, 0, v___x_2801_);
return v___f_2802_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11(void){
_start:
{
lean_object* v___f_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; 
v___f_2803_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10);
v___f_2804_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___f_2804_);
lean_ctor_set(v___x_2805_, 1, v___f_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11);
v___x_2807_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* v_t_2808_, lean_object* v_tp_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2817_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12);
lean_inc_ref(v_tp_2809_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_tp_2809_);
v___x_2819_ = 1;
v___x_2820_ = lean_box(0);
v___x_2821_ = l_Lean_Elab_Term_elabTermEnsuringType(v_t_2808_, v___x_2818_, v___x_2819_, v___x_2819_, v___x_2820_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; uint8_t v___x_2830_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2830_ = l_Lean_Expr_hasSyntheticSorry(v_a_2822_);
if (v___x_2830_ == 0)
{
v___y_2824_ = v_a_2812_;
v___y_2825_ = v_a_2813_;
v___y_2826_ = v_a_2814_;
v___y_2827_ = v_a_2815_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_250__overap_2831_; lean_object* v___x_2832_; 
v___x_250__overap_2831_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_2817_);
lean_inc(v_a_2815_);
lean_inc_ref(v_a_2814_);
lean_inc(v_a_2813_);
lean_inc_ref(v_a_2812_);
lean_inc(v_a_2811_);
lean_inc_ref(v_a_2810_);
v___x_2832_ = lean_apply_7(v___x_250__overap_2831_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, lean_box(0));
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_dec_ref_known(v___x_2832_, 1);
v___y_2824_ = v_a_2812_;
v___y_2825_ = v_a_2813_;
v___y_2826_ = v_a_2814_;
v___y_2827_ = v_a_2815_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2822_);
lean_dec_ref(v_tp_2809_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
v___jp_2823_:
{
uint8_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = 1;
v___x_2829_ = l_Lean_Meta_evalExpr___redArg(v_tp_2809_, v_a_2822_, v___x_2828_, v___x_2819_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2829_;
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref(v_tp_2809_);
v_a_2841_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2821_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2821_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object* v_t_2849_, lean_object* v_tp_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2849_, v_tp_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg(){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* v_00_u03b1_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* v_00_u03b1_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
return v_res_2873_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_box(0);
v___x_2875_ = l_Lean_Elab_abortTermExceptionId;
v___x_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* v_00_u03b1_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* v_00_u03b1_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v_00_u03b1_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; lean_object* v_env_2903_; lean_object* v___x_2904_; lean_object* v_mainModule_2905_; lean_object* v___x_2906_; 
v___x_2902_ = lean_st_ref_get(v___y_2900_);
v_env_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc_ref(v_env_2903_);
lean_dec(v___x_2902_);
v___x_2904_ = l_Lean_Environment_header(v_env_2903_);
lean_dec_ref(v_env_2903_);
v_mainModule_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_mainModule_2905_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_mainModule_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_2907_);
lean_dec(v___y_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* v___x_2918_, lean_object* v___x_2919_, uint8_t v___x_2920_, lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_inc_ref(v___x_2918_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2918_);
v___x_2930_ = lean_box(0);
v___x_2931_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2919_, v___x_2929_, v___x_2920_, v___x_2920_, v___x_2930_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; uint8_t v___x_2940_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2931_, 1);
v___x_2940_ = l_Lean_Expr_hasSyntheticSorry(v_a_2932_);
if (v___x_2940_ == 0)
{
v___y_2934_ = v___y_2924_;
v___y_2935_ = v___y_2925_;
v___y_2936_ = v___y_2926_;
v___y_2937_ = v___y_2927_;
goto v___jp_2933_;
}
else
{
lean_object* v___x_2941_; lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2918_);
v___x_2941_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
v___jp_2933_:
{
uint8_t v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = 1;
v___x_2939_ = l_Lean_Meta_evalExpr___redArg(v___x_2918_, v_a_2932_, v___x_2938_, v___x_2920_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2939_;
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v___x_2918_);
v_a_2950_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2931_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2931_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v_x_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
uint8_t v___x_8969__boxed_2969_; lean_object* v_res_2970_; 
v___x_8969__boxed_2969_ = lean_unbox(v___x_2960_);
v_res_2970_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(v___x_2958_, v___x_2959_, v___x_8969__boxed_2969_, v_x_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_x_2961_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(lean_object* v_msgData_2971_, lean_object* v_macroStack_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_scopes_2977_; lean_object* v___x_2978_; lean_object* v_opts_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2975_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2976_ = lean_st_ref_get(v___y_2973_);
v_scopes_2977_ = lean_ctor_get(v___x_2976_, 2);
lean_inc(v_scopes_2977_);
lean_dec(v___x_2976_);
v___x_2978_ = l_List_head_x21___redArg(v___x_2975_, v_scopes_2977_);
lean_dec(v_scopes_2977_);
v_opts_2979_ = lean_ctor_get(v___x_2978_, 1);
lean_inc_ref(v_opts_2979_);
lean_dec(v___x_2978_);
v___x_2980_ = l_Lean_Elab_pp_macroStack;
v___x_2981_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_2979_, v___x_2980_);
lean_dec_ref(v_opts_2979_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_dec(v_macroStack_2972_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_msgData_2971_);
return v___x_2982_;
}
else
{
if (lean_obj_tag(v_macroStack_2972_) == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_msgData_2971_);
return v___x_2983_;
}
else
{
lean_object* v_head_2984_; lean_object* v_after_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3000_; 
v_head_2984_ = lean_ctor_get(v_macroStack_2972_, 0);
lean_inc(v_head_2984_);
v_after_2985_ = lean_ctor_get(v_head_2984_, 1);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_head_2984_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_head_2984_, 0);
lean_dec(v_unused_3001_);
v___x_2987_ = v_head_2984_;
v_isShared_2988_ = v_isSharedCheck_3000_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_after_2985_);
lean_dec(v_head_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3000_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 7);
lean_ctor_set(v___x_2987_, 1, v___x_2989_);
lean_ctor_set(v___x_2987_, 0, v_msgData_2971_);
v___x_2991_ = v___x_2987_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_msgData_2971_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_msgData_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2992_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = l_Lean_MessageData_ofSyntax(v_after_2985_);
v___x_2995_ = l_Lean_indentD(v___x_2994_);
v_msgData_2996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2996_, 0, v___x_2993_);
lean_ctor_set(v_msgData_2996_, 1, v___x_2995_);
v___x_2997_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_2996_, v_macroStack_2972_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg___boxed(lean_object* v_msgData_3002_, lean_object* v_macroStack_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_msgData_3002_, v_macroStack_3003_, v___y_3004_);
lean_dec(v___y_3004_);
return v_res_3006_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3(void){
_start:
{
size_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3015_ = ((size_t)5ULL);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_unsigned_to_nat(32u);
v___x_3018_ = lean_mk_empty_array_with_capacity(v___x_3017_);
v___x_3019_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2);
v___x_3020_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3018_);
lean_ctor_set(v___x_3020_, 2, v___x_3016_);
lean_ctor_set(v___x_3020_, 3, v___x_3016_);
lean_ctor_set_usize(v___x_3020_, 4, v___x_3015_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3021_ = lean_box(1);
v___x_3022_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3);
v___x_3023_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0);
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
lean_object* v___x_3028_; lean_object* v_env_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v_scopes_3032_; lean_object* v___x_3033_; lean_object* v_opts_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3028_ = lean_st_ref_get(v___y_3026_);
v_env_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc_ref(v_env_3029_);
lean_dec(v___x_3028_);
v___x_3030_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3031_ = lean_st_ref_get(v___y_3026_);
v_scopes_3032_ = lean_ctor_get(v___x_3031_, 2);
lean_inc(v_scopes_3032_);
lean_dec(v___x_3031_);
v___x_3033_ = l_List_head_x21___redArg(v___x_3030_, v_scopes_3032_);
lean_dec(v_scopes_3032_);
v_opts_3034_ = lean_ctor_get(v___x_3033_, 1);
lean_inc_ref(v_opts_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1);
v___x_3036_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4);
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
lean_object* v_a_3049_; lean_object* v_macroStack_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v_macroStack_3050_ = lean_ctor_get(v___y_3045_, 4);
v___x_3051_ = l_Lean_Elab_getBetterRef(v_a_3049_, v_macroStack_3050_);
lean_dec(v_a_3049_);
v___x_3052_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msg_3044_, v___y_3046_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
lean_inc(v_macroStack_3050_);
v___x_3054_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_a_3053_, v_macroStack_3050_, v___y_3046_);
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
lean_ctor_set(v___x_3059_, 0, v___x_3051_);
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
lean_object* v___x_3145_; lean_object* v___x_3146_; double v___x_3147_; uint8_t v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3145_ = lean_box(0);
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_3148_ = 0;
v___x_3149_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3150_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3150_, 0, v_cls_3111_);
lean_ctor_set(v___x_3150_, 1, v___x_3146_);
lean_ctor_set(v___x_3150_, 2, v___x_3149_);
lean_ctor_set_float(v___x_3150_, sizeof(void*)*3, v___x_3147_);
lean_ctor_set_float(v___x_3150_, sizeof(void*)*3 + 8, v___x_3147_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*3 + 16, v___x_3148_);
v___x_3151_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_3152_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v_a_3119_);
lean_ctor_set(v___x_3152_, 2, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v_a_3117_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = l_Lean_PersistentArray_push___redArg(v_traces_3141_, v___x_3153_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v___x_3154_);
v___x_3156_ = v___x_3143_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3154_);
lean_ctor_set_uint64(v_reuseFailAlloc_3164_, sizeof(void*)*1, v_tid_3140_);
v___x_3156_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 9, v___x_3156_);
v___x_3158_ = v___x_3138_;
goto v_reusejp_3157_;
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
lean_ctor_set(v_reuseFailAlloc_3163_, 9, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3163_, 10, v_snapshotTasks_3134_);
lean_ctor_set(v_reuseFailAlloc_3163_, 11, v_prevLinterStates_3135_);
lean_ctor_set(v_reuseFailAlloc_3163_, 12, v_codeQualityEntryTasks_3136_);
v___x_3158_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = lean_st_ref_put(v___y_3114_, v___x_3158_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3145_);
v___x_3161_ = v___x_3121_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3145_);
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
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_env_3190_; uint8_t v_isExporting_3191_; lean_object* v_entry_3192_; lean_object* v___x_3193_; lean_object* v_env_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___y_3199_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3188_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0);
v___x_3189_ = lean_st_ref_get(v___y_3186_);
v_env_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc_ref(v_env_3190_);
lean_dec(v___x_3189_);
v_isExporting_3191_ = lean_ctor_get_uint8(v_env_3190_, sizeof(void*)*8);
lean_dec_ref(v_env_3190_);
lean_inc(v_mod_3182_);
v_entry_3192_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3192_, 0, v_mod_3182_);
lean_ctor_set_uint8(v_entry_3192_, sizeof(void*)*1, v_isExporting_3191_);
lean_ctor_set_uint8(v_entry_3192_, sizeof(void*)*1 + 1, v_isMeta_3183_);
v___x_3193_ = lean_st_ref_get(v___y_3186_);
v_env_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc_ref(v_env_3194_);
lean_dec(v___x_3193_);
v___x_3195_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3196_ = lean_box(1);
v___x_3197_ = lean_box(0);
v___x_3227_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3188_, v___x_3195_, v_env_3194_, v___x_3196_, v___x_3197_);
v___x_3228_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_3227_, v_entry_3192_);
lean_dec(v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v_cls_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v_scopes_3253_; lean_object* v___x_3254_; lean_object* v_opts_3255_; uint8_t v_hasTrace_3256_; 
v_cls_3229_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6));
v___x_3230_ = l_Lean_inheritedTraceOptions;
v___x_3231_ = lean_st_ref_get(v___x_3230_);
v___x_3232_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3233_ = lean_st_ref_get(v___y_3186_);
v_scopes_3253_ = lean_ctor_get(v___x_3233_, 2);
lean_inc(v_scopes_3253_);
lean_dec(v___x_3233_);
v___x_3254_ = l_List_head_x21___redArg(v___x_3232_, v_scopes_3253_);
lean_dec(v_scopes_3253_);
v_opts_3255_ = lean_ctor_get(v___x_3254_, 1);
lean_inc_ref(v_opts_3255_);
lean_dec(v___x_3254_);
v_hasTrace_3256_ = lean_ctor_get_uint8(v_opts_3255_, sizeof(void*)*1);
if (v_hasTrace_3256_ == 0)
{
lean_dec_ref(v_opts_3255_);
lean_dec(v___x_3231_);
lean_dec(v_hint_3184_);
lean_dec(v_mod_3182_);
v___y_3199_ = v___y_3186_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3231_, v_opts_3255_, v___x_3257_);
lean_dec_ref(v_opts_3255_);
lean_dec(v___x_3231_);
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
v___x_3259_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
if (v_isExporting_3191_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_3261_ = v___x_3268_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
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
v___x_3264_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
if (v_isMeta_3183_ == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___y_3240_ = v___x_3265_;
v___y_3241_ = v___x_3266_;
goto v___jp_3239_;
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18));
v___y_3240_ = v___x_3265_;
v___y_3241_ = v___x_3267_;
goto v___jp_3239_;
}
}
}
}
v___jp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___y_3235_);
lean_ctor_set(v___x_3237_, 1, v___y_3236_);
v___x_3238_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_3229_, v___x_3237_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_dec_ref_known(v___x_3238_, 1);
v___y_3199_ = v___y_3186_;
goto v___jp_3198_;
}
else
{
lean_dec_ref_known(v_entry_3192_, 1);
return v___x_3238_;
}
}
v___jp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
lean_inc_ref(v___y_3241_);
v___x_3242_ = l_Lean_stringToMessageData(v___y_3241_);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___y_3240_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_MessageData_ofName(v_mod_3182_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_Name_isAnonymous(v_hint_3184_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_3250_ = l_Lean_MessageData_ofName(v_hint_3184_);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___y_3235_ = v___x_3247_;
v___y_3236_ = v___x_3251_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3252_; 
lean_dec(v_hint_3184_);
v___x_3252_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11);
v___y_3235_ = v___x_3247_;
v___y_3236_ = v___x_3252_;
goto v___jp_3234_;
}
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec_ref_known(v_entry_3192_, 1);
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
lean_object* v_asyncMode_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v_asyncMode_3218_ = lean_ctor_get(v_toEnvExtension_3201_, 2);
v___x_3219_ = lean_box(0);
v___x_3220_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3195_, v_env_3202_, v_entry_3192_, v_asyncMode_3218_, v___x_3197_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3220_);
v___x_3222_ = v___x_3216_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3220_);
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
v___x_3222_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_st_ref_put(v___y_3199_, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3219_);
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
lean_object* v___x_3291_; lean_object* v_modules_3292_; lean_object* v___x_3293_; lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v_toImport_3296_; lean_object* v_module_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; 
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
v___x_3298_ = lean_box(0);
v___x_3299_ = 0;
lean_inc(v_declName_3281_);
v___x_3300_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3297_, v___x_3299_, v_declName_3281_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3300_) == 0)
{
size_t v___x_3301_; size_t v___x_3302_; 
lean_dec_ref_known(v___x_3300_, 1);
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3284_, v___x_3301_);
v_i_3284_ = v___x_3302_;
v_b_3285_ = v___x_3298_;
goto _start;
}
else
{
lean_dec(v_declName_3281_);
return v___x_3300_;
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
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v_env_3326_; lean_object* v___y_3328_; lean_object* v___x_3341_; 
v___x_3321_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0);
v___x_3322_ = lean_st_ref_get(v___y_3319_);
v_env_3326_ = lean_ctor_get(v___x_3322_, 0);
lean_inc_ref(v_env_3326_);
lean_dec(v___x_3322_);
v___x_3341_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3326_, v_declName_3316_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_dec_ref(v_env_3326_);
lean_dec(v_declName_3316_);
goto v___jp_3323_;
}
else
{
lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v_modules_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v_val_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = l_Lean_Environment_header(v_env_3326_);
v_modules_3344_ = lean_ctor_get(v___x_3343_, 3);
lean_inc_ref(v_modules_3344_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = lean_array_get_size(v_modules_3344_);
v___x_3346_ = lean_nat_dec_lt(v_val_3342_, v___x_3345_);
if (v___x_3346_ == 0)
{
lean_dec_ref(v_modules_3344_);
lean_dec(v_val_3342_);
lean_dec_ref(v_env_3326_);
lean_dec(v_declName_3316_);
goto v___jp_3323_;
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___y_3350_; 
v___x_3347_ = lean_array_fget(v_modules_3344_, v_val_3342_);
lean_dec(v_val_3342_);
lean_dec_ref(v_modules_3344_);
v___x_3348_ = lean_st_ref_get(v___y_3319_);
if (v_isMeta_3317_ == 0)
{
lean_dec(v___x_3348_);
v___y_3350_ = v_isMeta_3317_;
goto v___jp_3349_;
}
else
{
lean_object* v_env_3361_; uint8_t v___x_3362_; 
v_env_3361_ = lean_ctor_get(v___x_3348_, 0);
lean_inc_ref(v_env_3361_);
lean_dec(v___x_3348_);
lean_inc(v_declName_3316_);
v___x_3362_ = l_Lean_isMarkedMeta(v_env_3361_, v_declName_3316_);
if (v___x_3362_ == 0)
{
v___y_3350_ = v_isMeta_3317_;
goto v___jp_3349_;
}
else
{
uint8_t v___x_3363_; 
v___x_3363_ = 0;
v___y_3350_ = v___x_3363_;
goto v___jp_3349_;
}
}
v___jp_3349_:
{
lean_object* v_toImport_3351_; lean_object* v_module_3352_; lean_object* v___x_3353_; 
v_toImport_3351_ = lean_ctor_get(v___x_3347_, 0);
lean_inc_ref(v_toImport_3351_);
lean_dec(v___x_3347_);
v_module_3352_ = lean_ctor_get(v_toImport_3351_, 0);
lean_inc(v_module_3352_);
lean_dec_ref(v_toImport_3351_);
lean_inc(v_declName_3316_);
v___x_3353_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3352_, v___y_3350_, v_declName_3316_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref_known(v___x_3353_, 1);
v___x_3354_ = l_Lean_indirectModUseExt;
v___x_3355_ = lean_box(1);
v___x_3356_ = lean_box(0);
lean_inc_ref(v_env_3326_);
v___x_3357_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3321_, v___x_3354_, v_env_3326_, v___x_3355_, v___x_3356_);
v___x_3358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_3357_, v_declName_3316_);
lean_dec(v___x_3357_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___y_3328_ = v___x_3359_;
goto v___jp_3327_;
}
else
{
lean_object* v_val_3360_; 
v_val_3360_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v___x_3358_, 1);
v___y_3328_ = v_val_3360_;
goto v___jp_3327_;
}
}
else
{
lean_dec_ref(v_env_3326_);
lean_dec(v_declName_3316_);
return v___x_3353_;
}
}
}
}
v___jp_3323_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
v___jp_3327_:
{
lean_object* v___x_3329_; size_t v_sz_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3329_ = lean_box(0);
v_sz_3330_ = lean_array_size(v___y_3328_);
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_3326_, v_declName_3316_, v___y_3328_, v_sz_3330_, v___x_3331_, v___x_3329_, v___y_3318_, v___y_3319_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v_env_3326_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; 
v_unused_3340_ = lean_ctor_get(v___x_3332_, 0);
lean_dec(v_unused_3340_);
v___x_3334_ = v___x_3332_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_dec(v___x_3332_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3329_);
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3329_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
else
{
return v___x_3332_;
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
lean_object* v___x_3498_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v_cmd_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___x_3574_; 
v___x_3498_ = lean_box(1);
v_cmd_3545_ = l_Lean_Syntax_getArg(v_x_3411_, v___x_3471_);
v___x_3546_ = lean_unsigned_to_nat(3u);
v___x_3547_ = l_Lean_Syntax_getArg(v_x_3411_, v___x_3546_);
lean_dec(v_x_3411_);
v___x_3574_ = l_Lean_Elab_Command_getRef___redArg(v_a_3412_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v_fileName_3576_; lean_object* v_fileMap_3577_; lean_object* v_currRecDepth_3578_; lean_object* v_cmdPos_3579_; lean_object* v_macroStack_3580_; lean_object* v_quotContext_x3f_3581_; lean_object* v_currMacroScope_3582_; lean_object* v_snap_x3f_3583_; lean_object* v_cancelTk_x3f_3584_; uint8_t v_suppressElabErrors_3585_; lean_object* v_ref_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_env_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v_fileName_3576_ = lean_ctor_get(v_a_3412_, 0);
v_fileMap_3577_ = lean_ctor_get(v_a_3412_, 1);
v_currRecDepth_3578_ = lean_ctor_get(v_a_3412_, 2);
v_cmdPos_3579_ = lean_ctor_get(v_a_3412_, 3);
v_macroStack_3580_ = lean_ctor_get(v_a_3412_, 4);
v_quotContext_x3f_3581_ = lean_ctor_get(v_a_3412_, 5);
v_currMacroScope_3582_ = lean_ctor_get(v_a_3412_, 6);
v_snap_x3f_3583_ = lean_ctor_get(v_a_3412_, 8);
v_cancelTk_x3f_3584_ = lean_ctor_get(v_a_3412_, 9);
v_suppressElabErrors_3585_ = lean_ctor_get_uint8(v_a_3412_, sizeof(void*)*10);
v_ref_3586_ = l_Lean_replaceRef(v_cmd_3545_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec(v_cmd_3545_);
lean_inc(v_cancelTk_x3f_3584_);
lean_inc(v_snap_x3f_3583_);
lean_inc(v_currMacroScope_3582_);
lean_inc(v_quotContext_x3f_3581_);
lean_inc(v_macroStack_3580_);
lean_inc(v_cmdPos_3579_);
lean_inc(v_currRecDepth_3578_);
lean_inc_ref(v_fileMap_3577_);
lean_inc_ref(v_fileName_3576_);
v___x_3587_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3587_, 0, v_fileName_3576_);
lean_ctor_set(v___x_3587_, 1, v_fileMap_3577_);
lean_ctor_set(v___x_3587_, 2, v_currRecDepth_3578_);
lean_ctor_set(v___x_3587_, 3, v_cmdPos_3579_);
lean_ctor_set(v___x_3587_, 4, v_macroStack_3580_);
lean_ctor_set(v___x_3587_, 5, v_quotContext_x3f_3581_);
lean_ctor_set(v___x_3587_, 6, v_currMacroScope_3582_);
lean_ctor_set(v___x_3587_, 7, v_ref_3586_);
lean_ctor_set(v___x_3587_, 8, v_snap_x3f_3583_);
lean_ctor_set(v___x_3587_, 9, v_cancelTk_x3f_3584_);
lean_ctor_set_uint8(v___x_3587_, sizeof(void*)*10, v_suppressElabErrors_3585_);
v___x_3588_ = lean_st_ref_get(v_a_3413_);
v_env_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc_ref(v_env_3589_);
lean_dec(v___x_3588_);
v___x_3590_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3591_ = l_Lean_Environment_contains(v_env_3589_, v___x_3590_, v___x_3496_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec(v___x_3547_);
lean_dec(v_id_3475_);
v___x_3592_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
v___x_3593_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v___x_3592_, v___x_3587_, v_a_3413_);
lean_dec_ref_known(v___x_3587_, 10);
return v___x_3593_;
}
else
{
v___y_3549_ = v___x_3587_;
v___y_3550_ = v_a_3413_;
goto v___jp_3548_;
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v___x_3547_);
lean_dec(v_cmd_3545_);
lean_dec(v_id_3475_);
v_a_3594_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3574_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3574_);
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
v___jp_3499_:
{
lean_object* v___x_3504_; lean_object* v_env_3505_; lean_object* v___x_3506_; lean_object* v_toEnvExtension_3507_; lean_object* v_asyncMode_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3504_ = lean_st_ref_get(v___y_3503_);
v_env_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc_ref(v_env_3505_);
lean_dec(v___x_3504_);
v___x_3506_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3507_ = lean_ctor_get(v___x_3506_, 0);
v_asyncMode_3508_ = lean_ctor_get(v_toEnvExtension_3507_, 2);
v___x_3509_ = lean_box(0);
v___x_3510_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3498_, v___x_3506_, v_env_3505_, v_asyncMode_3508_, v___x_3509_);
v___x_3511_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_3501_, v___x_3510_);
lean_dec(v___x_3510_);
if (v___x_3511_ == 0)
{
v___y_3487_ = v___y_3500_;
v___y_3488_ = v___y_3501_;
v___y_3489_ = v___y_3502_;
v___y_3490_ = v___y_3503_;
goto v___jp_3486_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec_ref(v___y_3500_);
v___x_3512_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
v___x_3513_ = l_Lean_MessageData_ofName(v___y_3501_);
v___x_3514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3514_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3516_, v___y_3502_, v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v_id_3475_);
return v___x_3517_;
}
}
v___jp_3518_:
{
lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3523_ = l_Lean_Name_getNumParts(v___y_3520_);
v___x_3524_ = lean_nat_dec_eq(v___x_3523_, v___x_3474_);
lean_dec(v___x_3523_);
if (v___x_3524_ == 0)
{
if (v___x_3472_ == 0)
{
v___y_3500_ = v___y_3519_;
v___y_3501_ = v___y_3520_;
v___y_3502_ = v___y_3521_;
v___y_3503_ = v___y_3522_;
goto v___jp_3499_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_dec_ref(v___y_3519_);
v___x_3525_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
v___x_3526_ = l_Lean_MessageData_ofName(v___y_3520_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3531_, v___y_3521_, v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v_id_3475_);
return v___x_3532_;
}
}
else
{
v___y_3500_ = v___y_3519_;
v___y_3501_ = v___y_3520_;
v___y_3502_ = v___y_3521_;
v___y_3503_ = v___y_3522_;
goto v___jp_3499_;
}
}
v___jp_3533_:
{
uint8_t v___x_3538_; 
v___x_3538_ = l_Lean_Name_hasMacroScopes(v___y_3535_);
if (v___x_3538_ == 0)
{
v___y_3519_ = v___y_3534_;
v___y_3520_ = v___y_3535_;
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___y_3537_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
v___x_3539_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
lean_inc(v_id_3475_);
v___x_3540_ = l_Lean_MessageData_ofSyntax(v_id_3475_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
v___x_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3543_, v___y_3536_, v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v_id_3475_);
return v___x_3544_;
}
}
v___jp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3552_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_3551_, v___x_3496_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___f_3555_; lean_object* v___x_3556_; 
lean_dec_ref_known(v___x_3552_, 1);
v___x_3553_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
v___x_3554_ = lean_box(v___x_3496_);
v___f_3555_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3555_, 0, v___x_3553_);
lean_closure_set(v___f_3555_, 1, v___x_3547_);
lean_closure_set(v___f_3555_, 2, v___x_3554_);
v___x_3556_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3555_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v___x_3558_ = l_Lean_TSyntax_getId(v_id_3475_);
v___x_3559_ = l_Lean_Name_isAnonymous(v___x_3558_);
if (v___x_3559_ == 0)
{
v___y_3534_ = v_a_3557_;
v___y_3535_ = v___x_3558_;
v___y_3536_ = v___y_3549_;
v___y_3537_ = v___y_3550_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec(v___x_3558_);
lean_dec(v_a_3557_);
v___x_3560_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
lean_inc(v_id_3475_);
v___x_3561_ = l_Lean_MessageData_ofSyntax(v_id_3475_);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3475_, v___x_3564_, v___y_3549_, v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v_id_3475_);
return v___x_3565_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec_ref(v___y_3549_);
lean_dec(v_id_3475_);
v_a_3566_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3556_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3556_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_dec_ref(v___y_3549_);
lean_dec(v___x_3547_);
lean_dec(v_id_3475_);
return v___x_3552_;
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
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v_env_3432_; lean_object* v_messages_3433_; lean_object* v_scopes_3434_; lean_object* v_usedQuotCtxts_3435_; lean_object* v_nextMacroScope_3436_; lean_object* v_maxRecDepth_3437_; lean_object* v_ngen_3438_; lean_object* v_auxDeclNGen_3439_; lean_object* v_infoState_3440_; lean_object* v_traceState_3441_; lean_object* v_snapshotTasks_3442_; lean_object* v_prevLinterStates_3443_; lean_object* v_codeQualityEntryTasks_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3464_; 
v___x_3428_ = l_Lean_DeclarationRange_ofStringPositions(v___y_3419_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec(v___y_3421_);
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v_a_3424_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
v___x_3431_ = lean_st_ref_take(v___y_3416_);
v_env_3432_ = lean_ctor_get(v___x_3431_, 0);
v_messages_3433_ = lean_ctor_get(v___x_3431_, 1);
v_scopes_3434_ = lean_ctor_get(v___x_3431_, 2);
v_usedQuotCtxts_3435_ = lean_ctor_get(v___x_3431_, 3);
v_nextMacroScope_3436_ = lean_ctor_get(v___x_3431_, 4);
v_maxRecDepth_3437_ = lean_ctor_get(v___x_3431_, 5);
v_ngen_3438_ = lean_ctor_get(v___x_3431_, 6);
v_auxDeclNGen_3439_ = lean_ctor_get(v___x_3431_, 7);
v_infoState_3440_ = lean_ctor_get(v___x_3431_, 8);
v_traceState_3441_ = lean_ctor_get(v___x_3431_, 9);
v_snapshotTasks_3442_ = lean_ctor_get(v___x_3431_, 10);
v_prevLinterStates_3443_ = lean_ctor_get(v___x_3431_, 11);
v_codeQualityEntryTasks_3444_ = lean_ctor_get(v___x_3431_, 12);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3446_ = v___x_3431_;
v_isShared_3447_ = v_isSharedCheck_3464_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3444_);
lean_inc(v_prevLinterStates_3443_);
lean_inc(v_snapshotTasks_3442_);
lean_inc(v_traceState_3441_);
lean_inc(v_infoState_3440_);
lean_inc(v_auxDeclNGen_3439_);
lean_inc(v_ngen_3438_);
lean_inc(v_maxRecDepth_3437_);
lean_inc(v_nextMacroScope_3436_);
lean_inc(v_usedQuotCtxts_3435_);
lean_inc(v_scopes_3434_);
lean_inc(v_messages_3433_);
lean_inc(v_env_3432_);
lean_dec(v___x_3431_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3464_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v_toEnvExtension_3449_; lean_object* v_asyncMode_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3448_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3449_ = lean_ctor_get(v___x_3448_, 0);
v_asyncMode_3450_ = lean_ctor_get(v_toEnvExtension_3449_, 2);
v___x_3451_ = lean_box(0);
v___x_3452_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v___y_3417_);
lean_ctor_set(v___x_3453_, 2, v___x_3430_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___y_3420_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_box(0);
v___x_3456_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3448_, v_env_3432_, v___x_3454_, v_asyncMode_3450_, v___x_3455_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3456_);
v___x_3458_ = v___x_3446_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_messages_3433_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_scopes_3434_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_usedQuotCtxts_3435_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_nextMacroScope_3436_);
lean_ctor_set(v_reuseFailAlloc_3463_, 5, v_maxRecDepth_3437_);
lean_ctor_set(v_reuseFailAlloc_3463_, 6, v_ngen_3438_);
lean_ctor_set(v_reuseFailAlloc_3463_, 7, v_auxDeclNGen_3439_);
lean_ctor_set(v_reuseFailAlloc_3463_, 8, v_infoState_3440_);
lean_ctor_set(v_reuseFailAlloc_3463_, 9, v_traceState_3441_);
lean_ctor_set(v_reuseFailAlloc_3463_, 10, v_snapshotTasks_3442_);
lean_ctor_set(v_reuseFailAlloc_3463_, 11, v_prevLinterStates_3443_);
lean_ctor_set(v_reuseFailAlloc_3463_, 12, v_codeQualityEntryTasks_3444_);
v___x_3458_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3459_ = lean_st_ref_put(v___y_3416_, v___x_3458_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3451_);
v___x_3461_ = v___x_3426_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3451_);
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
