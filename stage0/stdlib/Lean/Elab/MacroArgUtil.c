// Lean compiler output
// Module: Lean.Elab.MacroArgUtil
// Imports: public import Lean.Elab.Syntax
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Parser_getParserAliasInfo(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unary"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 77, 42, 108, 13, 102, 39, 65)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__8_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1_value;
static const lean_array_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strLit"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__4 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "unknown parser declaration/category/alias `"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nonReserved"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__2 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 78, 166, 169, 121, 44, 215, 226)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__9 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(195, 96, 22, 193, 32, 12, 216, 27)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sepBy1"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__11 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 224, 0, 238, 204, 234, 239, 47)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__19 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__19_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__21 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__21_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__23 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__23_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__25 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__25_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__30 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__30_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__32 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__32_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "token_antiquot"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__35 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__35_value;
static const lean_ctor_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__35_value),LEAN_SCALAR_PTR_LITERAL(33, 159, 231, 44, 235, 156, 55, 135)}};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36_value;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38;
static const lean_string_object l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39 = (const lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39_value;
static lean_once_cell_t l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_expandMacroArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMacroArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Command_expandMacroArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_expandMacroArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_expandMacroArg___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_expandMacroArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_expandMacroArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "macroArg"};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(198, 202, 94, 136, 146, 138, 176, 98)}};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___closed__3 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_expandMacroArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___closed__4 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Command_expandMacroArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandMacroArg___closed__5;
static const lean_ctor_object l_Lean_Elab_Command_expandMacroArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Command_expandMacroArg___closed__6 = (const lean_object*)&l_Lean_Elab_Command_expandMacroArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = lean_nat_dec_eq(v_val_6_, v_val_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(lean_object* v_00___16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(lean_object* v_id_18_, lean_object* v___x_19_, uint8_t v___x_20_, uint8_t v___x_21_, lean_object* v_x_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = l_Lean_TSyntax_getId(v_id_18_);
v___x_27_ = l_Lean_Parser_getParserAliasInfo(v___x_26_);
lean_dec(v___x_26_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_43_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_stackSz_x3f_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_stackSz_x3f_32_ = lean_ctor_get(v_a_28_, 1);
lean_inc(v_stackSz_x3f_32_);
lean_dec(v_a_28_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_19_);
v___x_34_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_32_, v___x_33_);
lean_dec_ref(v___x_33_);
lean_dec(v_stackSz_x3f_32_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_box(v___x_20_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_35_);
v___x_37_ = v___x_30_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
else
{
lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_39_ = lean_box(v___x_21_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_39_);
v___x_41_ = v___x_30_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_56_; 
lean_dec(v___x_19_);
v_a_44_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_56_ == 0)
{
v___x_46_ = v___x_27_;
v_isShared_47_ = v_isSharedCheck_56_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_27_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_56_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_ref_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v_ref_48_ = lean_ctor_get(v___y_23_, 7);
v___x_49_ = lean_io_error_to_string(v_a_44_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
v___x_51_ = l_Lean_MessageData_ofFormat(v___x_50_);
lean_inc(v_ref_48_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v_ref_48_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_52_);
v___x_54_ = v___x_46_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0___boxed(lean_object* v_id_57_, lean_object* v___x_58_, lean_object* v___x_59_, lean_object* v___x_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
uint8_t v___x_27956__boxed_65_; uint8_t v___x_27957__boxed_66_; lean_object* v_res_67_; 
v___x_27956__boxed_65_ = lean_unbox(v___x_59_);
v___x_27957__boxed_66_ = lean_unbox(v___x_60_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_57_, v___x_58_, v___x_27956__boxed_65_, v___x_27957__boxed_66_, v_x_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v_id_57_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(uint8_t v___x_90_, lean_object* v_as_91_, size_t v_i_92_, size_t v_stop_93_, lean_object* v_b_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_a_99_; uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_92_, v_stop_93_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v_a_111_; lean_object* v___y_113_; uint8_t v___x_124_; 
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_array_uget_borrowed(v_as_91_, v_i_92_);
lean_inc(v___x_107_);
v___x_124_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_104_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_107_);
v___x_126_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_125_);
if (v___x_126_ == 0)
{
goto v___jp_108_;
}
else
{
lean_object* v_id_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_id_127_ = l_Lean_Syntax_getArg(v___x_107_, v___x_105_);
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_127_);
v___x_129_ = l_Lean_Syntax_isOfKind(v_id_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_dec(v_id_127_);
goto v___jp_108_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_130_ = lean_unsigned_to_nat(2u);
v___x_131_ = l_Lean_Syntax_getArg(v___x_107_, v___x_130_);
v___x_132_ = l_Lean_Syntax_matchesNull(v___x_131_, v___x_106_);
if (v___x_132_ == 0)
{
lean_dec(v_id_127_);
goto v___jp_108_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = l_Lean_TSyntax_getId(v_id_127_);
lean_dec(v_id_127_);
v___x_134_ = l_Lean_Parser_getParserAliasInfo(v___x_133_);
lean_dec(v___x_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v_stackSz_x3f_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref(v___x_134_);
v_stackSz_x3f_136_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_stackSz_x3f_136_);
lean_dec(v_a_135_);
v___x_137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_138_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_136_, v___x_137_);
lean_dec(v_stackSz_x3f_136_);
if (v___x_138_ == 0)
{
v_a_111_ = v___x_129_;
goto v___jp_110_;
}
else
{
v_a_111_ = v___x_124_;
goto v___jp_110_;
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
lean_dec_ref(v_b_94_);
v_a_139_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v___x_134_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_134_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_ref_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v_ref_143_ = lean_ctor_get(v___y_95_, 7);
v___x_144_ = lean_io_error_to_string(v_a_139_);
v___x_145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
v___x_146_ = l_Lean_MessageData_ofFormat(v___x_145_);
lean_inc(v_ref_143_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_ref_143_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_id_152_ = l_Lean_Syntax_getArg(v___x_107_, v___x_105_);
v___x_153_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_152_);
v___x_154_ = l_Lean_Syntax_isOfKind(v_id_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_id_152_);
goto v___jp_108_;
}
else
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = l_Lean_Syntax_getArg(v___x_107_, v___x_106_);
v___x_156_ = l_Lean_Syntax_isNone(v___x_155_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
lean_inc(v___x_155_);
v___x_157_ = l_Lean_Syntax_matchesNull(v___x_155_, v___x_106_);
if (v___x_157_ == 0)
{
lean_dec(v___x_155_);
lean_dec(v_id_152_);
goto v___jp_108_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_159_ = l_Lean_Syntax_getArg(v___x_155_, v___x_105_);
lean_dec(v___x_155_);
v___x_160_ = l_Lean_Syntax_isOfKind(v___x_159_, v___x_158_);
if (v___x_160_ == 0)
{
lean_dec(v_id_152_);
goto v___jp_108_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_152_, v___x_105_, v___x_154_, v___x_90_, v___x_161_, v___y_95_, v___y_96_);
lean_dec(v_id_152_);
v___y_113_ = v___x_162_;
goto v___jp_112_;
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v___x_155_);
v___x_163_ = lean_box(0);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_152_, v___x_105_, v___x_154_, v___x_90_, v___x_163_, v___y_95_, v___y_96_);
lean_dec(v_id_152_);
v___y_113_ = v___x_164_;
goto v___jp_112_;
}
}
}
v___jp_108_:
{
lean_object* v___x_109_; 
lean_inc(v___x_107_);
v___x_109_ = lean_array_push(v_b_94_, v___x_107_);
v_a_99_ = v___x_109_;
goto v___jp_98_;
}
v___jp_110_:
{
if (v_a_111_ == 0)
{
v_a_99_ = v_b_94_;
goto v___jp_98_;
}
else
{
goto v___jp_108_;
}
}
v___jp_112_:
{
if (lean_obj_tag(v___y_113_) == 0)
{
lean_object* v_a_114_; uint8_t v___x_115_; 
v_a_114_ = lean_ctor_get(v___y_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref(v___y_113_);
v___x_115_ = lean_unbox(v_a_114_);
lean_dec(v_a_114_);
v_a_111_ = v___x_115_;
goto v___jp_110_;
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v_b_94_);
v_a_116_ = lean_ctor_get(v___y_113_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___y_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___y_113_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___y_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v_b_94_);
return v___x_165_;
}
v___jp_98_:
{
size_t v___x_100_; size_t v___x_101_; 
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_add(v_i_92_, v___x_100_);
v_i_92_ = v___x_101_;
v_b_94_ = v_a_99_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object* v___x_166_, lean_object* v_as_167_, lean_object* v_i_168_, lean_object* v_stop_169_, lean_object* v_b_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
uint8_t v___x_28084__boxed_174_; size_t v_i_boxed_175_; size_t v_stop_boxed_176_; lean_object* v_res_177_; 
v___x_28084__boxed_174_ = lean_unbox(v___x_166_);
v_i_boxed_175_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_stop_boxed_176_ = lean_unbox_usize(v_stop_169_);
lean_dec(v_stop_169_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_28084__boxed_174_, v_as_167_, v_i_boxed_175_, v_stop_boxed_176_, v_b_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v_as_167_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(uint8_t v___x_178_, lean_object* v_as_179_, size_t v_i_180_, size_t v_stop_181_, lean_object* v_b_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_a_187_; uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_eq(v_i_180_, v_stop_181_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v_a_199_; lean_object* v___y_201_; uint8_t v___x_212_; 
v___x_192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_array_uget_borrowed(v_as_179_, v_i_180_);
lean_inc(v___x_195_);
v___x_212_ = l_Lean_Syntax_isOfKind(v___x_195_, v___x_192_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_195_);
v___x_214_ = l_Lean_Syntax_isOfKind(v___x_195_, v___x_213_);
if (v___x_214_ == 0)
{
goto v___jp_196_;
}
else
{
lean_object* v_id_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_id_215_ = l_Lean_Syntax_getArg(v___x_195_, v___x_193_);
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_215_);
v___x_217_ = l_Lean_Syntax_isOfKind(v_id_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_id_215_);
goto v___jp_196_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = l_Lean_Syntax_getArg(v___x_195_, v___x_218_);
v___x_220_ = l_Lean_Syntax_matchesNull(v___x_219_, v___x_194_);
if (v___x_220_ == 0)
{
lean_dec(v_id_215_);
goto v___jp_196_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = l_Lean_TSyntax_getId(v_id_215_);
lean_dec(v_id_215_);
v___x_222_ = l_Lean_Parser_getParserAliasInfo(v___x_221_);
lean_dec(v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v_stackSz_x3f_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_222_);
v_stackSz_x3f_224_ = lean_ctor_get(v_a_223_, 1);
lean_inc(v_stackSz_x3f_224_);
lean_dec(v_a_223_);
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_226_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_224_, v___x_225_);
lean_dec(v_stackSz_x3f_224_);
if (v___x_226_ == 0)
{
v_a_199_ = v___x_217_;
goto v___jp_198_;
}
else
{
v_a_199_ = v___x_212_;
goto v___jp_198_;
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v_b_182_);
v_a_227_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_239_ == 0)
{
v___x_229_ = v___x_222_;
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_222_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v_ref_231_ = lean_ctor_get(v___y_183_, 7);
v___x_232_ = lean_io_error_to_string(v_a_227_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = l_Lean_MessageData_ofFormat(v___x_233_);
lean_inc(v_ref_231_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_231_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_235_);
v___x_237_ = v___x_229_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_id_240_ = l_Lean_Syntax_getArg(v___x_195_, v___x_193_);
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_240_);
v___x_242_ = l_Lean_Syntax_isOfKind(v_id_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec(v_id_240_);
goto v___jp_196_;
}
else
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = l_Lean_Syntax_getArg(v___x_195_, v___x_194_);
v___x_244_ = l_Lean_Syntax_isNone(v___x_243_);
if (v___x_244_ == 0)
{
uint8_t v___x_245_; 
lean_inc(v___x_243_);
v___x_245_ = l_Lean_Syntax_matchesNull(v___x_243_, v___x_194_);
if (v___x_245_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_id_240_);
goto v___jp_196_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = l_Lean_Syntax_getArg(v___x_243_, v___x_193_);
lean_dec(v___x_243_);
v___x_247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_248_ = l_Lean_Syntax_isOfKind(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_id_240_);
goto v___jp_196_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_box(0);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_240_, v___x_193_, v___x_242_, v___x_178_, v___x_249_, v___y_183_, v___y_184_);
lean_dec(v_id_240_);
v___y_201_ = v___x_250_;
goto v___jp_200_;
}
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v___x_243_);
v___x_251_ = lean_box(0);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_240_, v___x_193_, v___x_242_, v___x_178_, v___x_251_, v___y_183_, v___y_184_);
lean_dec(v_id_240_);
v___y_201_ = v___x_252_;
goto v___jp_200_;
}
}
}
v___jp_196_:
{
lean_object* v___x_197_; 
lean_inc(v___x_195_);
v___x_197_ = lean_array_push(v_b_182_, v___x_195_);
v_a_187_ = v___x_197_;
goto v___jp_186_;
}
v___jp_198_:
{
if (v_a_199_ == 0)
{
v_a_187_ = v_b_182_;
goto v___jp_186_;
}
else
{
goto v___jp_196_;
}
}
v___jp_200_:
{
if (lean_obj_tag(v___y_201_) == 0)
{
lean_object* v_a_202_; uint8_t v___x_203_; 
v_a_202_ = lean_ctor_get(v___y_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref(v___y_201_);
v___x_203_ = lean_unbox(v_a_202_);
lean_dec(v_a_202_);
v_a_199_ = v___x_203_;
goto v___jp_198_;
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_b_182_);
v_a_204_ = lean_ctor_get(v___y_201_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___y_201_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___y_201_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___y_201_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_b_182_);
return v___x_253_;
}
v___jp_186_:
{
size_t v___x_188_; size_t v___x_189_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_180_, v___x_188_);
v_i_180_ = v___x_189_;
v_b_182_ = v_a_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object* v___x_254_, lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
uint8_t v___x_28274__boxed_262_; size_t v_i_boxed_263_; size_t v_stop_boxed_264_; lean_object* v_res_265_; 
v___x_28274__boxed_262_ = lean_unbox(v___x_254_);
v_i_boxed_263_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_264_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_28274__boxed_262_, v_as_255_, v_i_boxed_263_, v_stop_boxed_264_, v_b_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec_ref(v_as_255_);
return v_res_265_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
lean_object* v_name_268_; lean_object* v_defValue_269_; lean_object* v_map_270_; lean_object* v___x_271_; 
v_name_268_ = lean_ctor_get(v_opt_267_, 0);
v_defValue_269_ = lean_ctor_get(v_opt_267_, 1);
v_map_270_ = lean_ctor_get(v_opts_266_, 0);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_270_, v_name_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
uint8_t v___x_272_; 
v___x_272_ = lean_unbox(v_defValue_269_);
return v___x_272_;
}
else
{
lean_object* v_val_273_; 
v_val_273_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_val_273_);
lean_dec_ref(v___x_271_);
if (lean_obj_tag(v_val_273_) == 1)
{
uint8_t v_v_274_; 
v_v_274_ = lean_ctor_get_uint8(v_val_273_, 0);
lean_dec_ref(v_val_273_);
return v_v_274_;
}
else
{
uint8_t v___x_275_; 
lean_dec(v_val_273_);
v___x_275_ = lean_unbox(v_defValue_269_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_276_, lean_object* v_opt_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_276_, v_opt_277_);
lean_dec_ref(v_opt_277_);
lean_dec_ref(v_opts_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_box(1);
v___x_281_ = l_Lean_MessageData_ofFormat(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2));
v___x_286_ = l_Lean_MessageData_ofFormat(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
return v_x_287_;
}
else
{
lean_object* v_head_289_; lean_object* v_tail_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_312_; 
v_head_289_ = lean_ctor_get(v_x_288_, 0);
v_tail_290_ = lean_ctor_get(v_x_288_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_312_ == 0)
{
v___x_292_ = v_x_288_;
v_isShared_293_ = v_isSharedCheck_312_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_tail_290_);
lean_inc(v_head_289_);
lean_dec(v_x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_312_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_before_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_310_; 
v_before_294_ = lean_ctor_get(v_head_289_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_head_289_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v_head_289_, 1);
lean_dec(v_unused_311_);
v___x_296_ = v_head_289_;
v_isShared_297_ = v_isSharedCheck_310_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_before_294_);
lean_dec(v_head_289_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_310_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 7);
lean_ctor_set(v___x_296_, 1, v___x_298_);
lean_ctor_set(v___x_296_, 0, v_x_287_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_x_287_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_309_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 7);
lean_ctor_set(v___x_292_, 1, v___x_301_);
lean_ctor_set(v___x_292_, 0, v___x_300_);
v___x_303_ = v___x_292_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_308_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = l_Lean_MessageData_ofSyntax(v_before_294_);
v___x_305_ = l_Lean_indentD(v___x_304_);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v_x_287_ = v___x_306_;
v_x_288_ = v_tail_290_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1));
v___x_317_ = l_Lean_MessageData_ofFormat(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(lean_object* v_msgData_318_, lean_object* v_macroStack_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v_scopes_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_opts_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_322_ = lean_st_ref_get(v___y_320_);
v_scopes_323_ = lean_ctor_get(v___x_322_, 2);
lean_inc(v_scopes_323_);
lean_dec(v___x_322_);
v___x_324_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_325_ = l_List_head_x21___redArg(v___x_324_, v_scopes_323_);
lean_dec(v_scopes_323_);
v_opts_326_ = lean_ctor_get(v___x_325_, 1);
lean_inc_ref(v_opts_326_);
lean_dec(v___x_325_);
v___x_327_ = l_Lean_Elab_pp_macroStack;
v___x_328_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_326_, v___x_327_);
lean_dec_ref(v_opts_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec(v_macroStack_319_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_msgData_318_);
return v___x_329_;
}
else
{
if (lean_obj_tag(v_macroStack_319_) == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_msgData_318_);
return v___x_330_;
}
else
{
lean_object* v_head_331_; lean_object* v_after_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_347_; 
v_head_331_ = lean_ctor_get(v_macroStack_319_, 0);
lean_inc(v_head_331_);
v_after_332_ = lean_ctor_get(v_head_331_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_head_331_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_head_331_, 0);
lean_dec(v_unused_348_);
v___x_334_ = v_head_331_;
v_isShared_335_ = v_isSharedCheck_347_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_after_332_);
lean_dec(v_head_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_347_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 7);
lean_ctor_set(v___x_334_, 1, v___x_336_);
lean_ctor_set(v___x_334_, 0, v_msgData_318_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_msgData_318_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_346_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_msgData_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_339_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_MessageData_ofSyntax(v_after_332_);
v___x_342_ = l_Lean_indentD(v___x_341_);
v_msgData_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_343_, 0, v___x_340_);
lean_ctor_set(v_msgData_343_, 1, v___x_342_);
v___x_344_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(v_msgData_343_, v_macroStack_319_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_349_, lean_object* v_macroStack_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_349_, v_macroStack_350_, v___y_351_);
lean_dec(v___y_351_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_354_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
lean_ctor_set(v___x_359_, 3, v___x_358_);
lean_ctor_set(v___x_359_, 4, v___x_357_);
lean_ctor_set(v___x_359_, 5, v___x_357_);
lean_ctor_set(v___x_359_, 6, v___x_357_);
lean_ctor_set(v___x_359_, 7, v___x_357_);
lean_ctor_set(v___x_359_, 8, v___x_357_);
lean_ctor_set(v___x_359_, 9, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_unsigned_to_nat(32u);
v___x_361_ = lean_mk_empty_array_with_capacity(v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_363_ = ((size_t)5ULL);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_unsigned_to_nat(32u);
v___x_366_ = lean_mk_empty_array_with_capacity(v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_368_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
lean_ctor_set(v___x_368_, 2, v___x_364_);
lean_ctor_set(v___x_368_, 3, v___x_364_);
lean_ctor_set_usize(v___x_368_, 4, v___x_363_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = lean_box(1);
v___x_370_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_env_377_; lean_object* v___x_378_; lean_object* v_scopes_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_opts_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = lean_st_ref_get(v___y_374_);
v_scopes_379_ = lean_ctor_get(v___x_378_, 2);
lean_inc(v_scopes_379_);
lean_dec(v___x_378_);
v___x_380_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_381_ = l_List_head_x21___redArg(v___x_380_, v_scopes_379_);
lean_dec(v_scopes_379_);
v_opts_382_ = lean_ctor_get(v___x_381_, 1);
lean_inc_ref(v_opts_382_);
lean_dec(v___x_381_);
v___x_383_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_384_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_385_, 0, v_env_377_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
lean_ctor_set(v___x_385_, 3, v_opts_382_);
v___x_386_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_msgData_373_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_388_, v___y_389_);
lean_dec(v___y_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Elab_Command_getRef___redArg(v___y_393_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_macroStack_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v___x_396_);
v_macroStack_398_ = lean_ctor_get(v___y_393_, 4);
v___x_399_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_392_, v___y_394_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_399_);
lean_inc_n(v_macroStack_398_, 2);
v___x_401_ = l_Lean_Elab_getBetterRef(v_a_397_, v_macroStack_398_);
lean_dec(v_a_397_);
v___x_402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_400_, v_macroStack_398_, v___y_394_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_401_);
lean_ctor_set(v___x_407_, 1, v_a_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v_msg_392_);
v_a_412_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_396_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_396_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t v___x_425_, lean_object* v_as_426_, size_t v_i_427_, size_t v_stop_428_, lean_object* v_b_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_a_434_; uint8_t v___x_438_; 
v___x_438_ = lean_usize_dec_eq(v_i_427_, v_stop_428_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v_a_444_; lean_object* v___y_446_; uint8_t v___x_457_; 
v___x_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_440_ = lean_array_uget_borrowed(v_as_426_, v_i_427_);
lean_inc(v___x_440_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_440_, v___x_439_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_440_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_440_, v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_441_;
}
else
{
lean_object* v___x_460_; lean_object* v_id_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v_id_461_ = l_Lean_Syntax_getArg(v___x_440_, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_461_);
v___x_463_ = l_Lean_Syntax_isOfKind(v_id_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v_id_461_);
goto v___jp_441_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_unsigned_to_nat(2u);
v___x_466_ = l_Lean_Syntax_getArg(v___x_440_, v___x_465_);
v___x_467_ = l_Lean_Syntax_matchesNull(v___x_466_, v___x_464_);
if (v___x_467_ == 0)
{
lean_dec(v_id_461_);
goto v___jp_441_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = l_Lean_TSyntax_getId(v_id_461_);
lean_dec(v_id_461_);
v___x_469_ = l_Lean_Parser_getParserAliasInfo(v___x_468_);
lean_dec(v___x_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v_stackSz_x3f_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
v_stackSz_x3f_471_ = lean_ctor_get(v_a_470_, 1);
lean_inc(v_stackSz_x3f_471_);
lean_dec(v_a_470_);
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_473_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_471_, v___x_472_);
lean_dec(v_stackSz_x3f_471_);
if (v___x_473_ == 0)
{
v_a_444_ = v___x_463_;
goto v___jp_443_;
}
else
{
v_a_444_ = v___x_457_;
goto v___jp_443_;
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_486_; 
lean_dec_ref(v_b_429_);
v_a_474_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_486_ == 0)
{
v___x_476_ = v___x_469_;
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_469_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_ref_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v_ref_478_ = lean_ctor_get(v___y_430_, 7);
v___x_479_ = lean_io_error_to_string(v_a_474_);
v___x_480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = l_Lean_MessageData_ofFormat(v___x_480_);
lean_inc(v_ref_478_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_ref_478_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_482_);
v___x_484_ = v___x_476_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_object* v___x_487_; lean_object* v_id_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v_id_488_ = l_Lean_Syntax_getArg(v___x_440_, v___x_487_);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_488_);
v___x_490_ = l_Lean_Syntax_isOfKind(v_id_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec(v_id_488_);
goto v___jp_441_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = l_Lean_Syntax_getArg(v___x_440_, v___x_491_);
v___x_493_ = l_Lean_Syntax_isNone(v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
lean_inc(v___x_492_);
v___x_494_ = l_Lean_Syntax_matchesNull(v___x_492_, v___x_491_);
if (v___x_494_ == 0)
{
lean_dec(v___x_492_);
lean_dec(v_id_488_);
goto v___jp_441_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = l_Lean_Syntax_getArg(v___x_492_, v___x_487_);
lean_dec(v___x_492_);
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_497_ = l_Lean_Syntax_isOfKind(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_dec(v_id_488_);
goto v___jp_441_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_box(0);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_488_, v___x_487_, v___x_490_, v___x_425_, v___x_498_, v___y_430_, v___y_431_);
lean_dec(v_id_488_);
v___y_446_ = v___x_499_;
goto v___jp_445_;
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v___x_492_);
v___x_500_ = lean_box(0);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_488_, v___x_487_, v___x_490_, v___x_425_, v___x_500_, v___y_430_, v___y_431_);
lean_dec(v_id_488_);
v___y_446_ = v___x_501_;
goto v___jp_445_;
}
}
}
v___jp_441_:
{
lean_object* v___x_442_; 
lean_inc(v___x_440_);
v___x_442_ = lean_array_push(v_b_429_, v___x_440_);
v_a_434_ = v___x_442_;
goto v___jp_433_;
}
v___jp_443_:
{
if (v_a_444_ == 0)
{
v_a_434_ = v_b_429_;
goto v___jp_433_;
}
else
{
goto v___jp_441_;
}
}
v___jp_445_:
{
if (lean_obj_tag(v___y_446_) == 0)
{
lean_object* v_a_447_; uint8_t v___x_448_; 
v_a_447_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref(v___y_446_);
v___x_448_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
v_a_444_ = v___x_448_;
goto v___jp_443_;
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec_ref(v_b_429_);
v_a_449_ = lean_ctor_get(v___y_446_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___y_446_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___y_446_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___y_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v_b_429_);
return v___x_502_;
}
v___jp_433_:
{
size_t v___x_435_; size_t v___x_436_; 
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_427_, v___x_435_);
v_i_427_ = v___x_436_;
v_b_429_ = v_a_434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v___x_503_, lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_, lean_object* v_b_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_28756__boxed_511_; size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v___x_28756__boxed_511_ = lean_unbox(v___x_503_);
v_i_boxed_512_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_28756__boxed_511_, v_as_504_, v_i_boxed_512_, v_stop_boxed_513_, v_b_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_as_504_);
return v_res_514_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_box(0);
v___x_528_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_536_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_a_536_, v___x_543_);
v___x_545_ = 1;
if (v___x_544_ == 0)
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_536_);
v___x_553_ = l_Lean_Syntax_isOfKind(v_a_536_, v___x_552_);
if (v___x_553_ == 0)
{
lean_dec(v_a_536_);
goto v___jp_546_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_a_559_; lean_object* v___y_565_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l_Lean_Syntax_getArg(v_a_536_, v___x_554_);
lean_dec(v_a_536_);
v___x_556_ = l_Lean_Syntax_getArgs(v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_array_get_size(v___x_556_);
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_577_ = lean_nat_dec_lt(v___x_557_, v___x_575_);
if (v___x_577_ == 0)
{
lean_dec_ref(v___x_556_);
v_a_559_ = v___x_576_;
goto v___jp_558_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = lean_nat_dec_le(v___x_575_, v___x_575_);
if (v___x_578_ == 0)
{
if (v___x_577_ == 0)
{
lean_dec_ref(v___x_556_);
v_a_559_ = v___x_576_;
goto v___jp_558_;
}
else
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_575_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_544_, v___x_556_, v___x_579_, v___x_580_, v___x_576_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_556_);
v___y_565_ = v___x_581_;
goto v___jp_564_;
}
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_575_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_544_, v___x_556_, v___x_582_, v___x_583_, v___x_576_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_556_);
v___y_565_ = v___x_584_;
goto v___jp_564_;
}
}
v___jp_558_:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_get_size(v_a_559_);
v___x_561_ = lean_nat_dec_eq(v___x_560_, v___x_554_);
if (v___x_561_ == 0)
{
lean_dec_ref(v_a_559_);
goto v___jp_546_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_array_fget(v_a_559_, v___x_557_);
lean_dec_ref(v_a_559_);
v_a_536_ = v___x_562_;
goto _start;
}
}
v___jp_564_:
{
if (lean_obj_tag(v___y_565_) == 0)
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v___y_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref(v___y_565_);
v_a_559_ = v_a_566_;
goto v___jp_558_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_a_537_);
v_a_567_ = lean_ctor_get(v___y_565_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___y_565_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___y_565_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___y_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
else
{
lean_object* v___x_585_; lean_object* v___y_597_; lean_object* v___y_603_; lean_object* v_id_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v_id_613_ = l_Lean_Syntax_getArg(v_a_536_, v___x_585_);
v___x_614_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_615_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_613_);
v___x_616_ = l_Lean_Syntax_isOfKind(v_id_613_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
lean_dec(v_id_613_);
v___x_617_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_536_);
v___x_618_ = l_Lean_Syntax_isOfKind(v_a_536_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_a_536_);
goto v___jp_608_;
}
else
{
lean_object* v___x_619_; lean_object* v_a_621_; lean_object* v___y_627_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_637_ = l_Lean_Syntax_getArg(v_a_536_, v___x_619_);
lean_dec(v_a_536_);
v___x_638_ = l_Lean_Syntax_getArgs(v___x_637_);
lean_dec(v___x_637_);
v___x_639_ = lean_array_get_size(v___x_638_);
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_641_ = lean_nat_dec_lt(v___x_585_, v___x_639_);
if (v___x_641_ == 0)
{
lean_dec_ref(v___x_638_);
v_a_621_ = v___x_640_;
goto v___jp_620_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_le(v___x_639_, v___x_639_);
if (v___x_642_ == 0)
{
if (v___x_641_ == 0)
{
lean_dec_ref(v___x_638_);
v_a_621_ = v___x_640_;
goto v___jp_620_;
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_639_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_616_, v___x_638_, v___x_643_, v___x_644_, v___x_640_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_638_);
v___y_627_ = v___x_645_;
goto v___jp_626_;
}
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_639_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_616_, v___x_638_, v___x_646_, v___x_647_, v___x_640_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_638_);
v___y_627_ = v___x_648_;
goto v___jp_626_;
}
}
v___jp_620_:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_a_621_);
v___x_623_ = lean_nat_dec_eq(v___x_622_, v___x_619_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_a_621_);
goto v___jp_608_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_array_fget(v_a_621_, v___x_585_);
lean_dec_ref(v_a_621_);
v_a_536_ = v___x_624_;
goto _start;
}
}
v___jp_626_:
{
if (lean_obj_tag(v___y_627_) == 0)
{
lean_object* v_a_628_; 
v_a_628_ = lean_ctor_get(v___y_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___y_627_);
v_a_621_ = v_a_628_;
goto v___jp_620_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_537_);
v_a_629_ = lean_ctor_get(v___y_627_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___y_627_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___y_627_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___y_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___x_731_; lean_object* v_a_733_; lean_object* v___y_739_; lean_object* v_a_750_; lean_object* v___y_756_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_766_ = l_Lean_Syntax_getArg(v_a_536_, v___x_731_);
v___x_767_ = l_Lean_Syntax_isNone(v___x_766_);
if (v___x_767_ == 0)
{
uint8_t v___x_768_; 
lean_inc(v___x_766_);
v___x_768_ = l_Lean_Syntax_matchesNull(v___x_766_, v___x_731_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; 
lean_dec(v_id_613_);
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_770_ = l_Lean_Syntax_isOfKind(v_a_536_, v___x_769_);
if (v___x_770_ == 0)
{
lean_dec(v___x_766_);
goto v___jp_591_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_771_ = l_Lean_Syntax_getArgs(v___x_766_);
lean_dec(v___x_766_);
v___x_772_ = lean_array_get_size(v___x_771_);
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_774_ = lean_nat_dec_lt(v___x_585_, v___x_772_);
if (v___x_774_ == 0)
{
lean_dec_ref(v___x_771_);
v_a_750_ = v___x_773_;
goto v___jp_749_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = lean_nat_dec_le(v___x_772_, v___x_772_);
if (v___x_775_ == 0)
{
if (v___x_774_ == 0)
{
lean_dec_ref(v___x_771_);
v_a_750_ = v___x_773_;
goto v___jp_749_;
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_of_nat(v___x_772_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_768_, v___x_771_, v___x_776_, v___x_777_, v___x_773_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_771_);
v___y_756_ = v___x_778_;
goto v___jp_755_;
}
}
else
{
size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((size_t)0ULL);
v___x_780_ = lean_usize_of_nat(v___x_772_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_768_, v___x_771_, v___x_779_, v___x_780_, v___x_773_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_771_);
v___y_756_ = v___x_781_;
goto v___jp_755_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = l_Lean_Syntax_getArg(v___x_766_, v___x_585_);
v___x_783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_784_ = l_Lean_Syntax_isOfKind(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; uint8_t v___x_786_; 
lean_dec(v_id_613_);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_786_ = l_Lean_Syntax_isOfKind(v_a_536_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec(v___x_766_);
goto v___jp_586_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_787_ = l_Lean_Syntax_getArgs(v___x_766_);
lean_dec(v___x_766_);
v___x_788_ = lean_array_get_size(v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_790_ = lean_nat_dec_lt(v___x_585_, v___x_788_);
if (v___x_790_ == 0)
{
lean_dec_ref(v___x_787_);
v_a_733_ = v___x_789_;
goto v___jp_732_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_le(v___x_788_, v___x_788_);
if (v___x_791_ == 0)
{
if (v___x_790_ == 0)
{
lean_dec_ref(v___x_787_);
v_a_733_ = v___x_789_;
goto v___jp_732_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_of_nat(v___x_788_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_784_, v___x_787_, v___x_792_, v___x_793_, v___x_789_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_787_);
v___y_739_ = v___x_794_;
goto v___jp_738_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_of_nat(v___x_788_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_784_, v___x_787_, v___x_795_, v___x_796_, v___x_789_, v_a_538_, v_a_539_);
lean_dec_ref(v___x_787_);
v___y_739_ = v___x_797_;
goto v___jp_738_;
}
}
}
}
else
{
lean_dec(v___x_766_);
lean_dec(v_a_536_);
v___y_650_ = v_a_538_;
v___y_651_ = v_a_539_;
goto v___jp_649_;
}
}
}
else
{
lean_dec(v___x_766_);
lean_dec(v_a_536_);
v___y_650_ = v_a_538_;
v___y_651_ = v_a_539_;
goto v___jp_649_;
}
v___jp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc(v_id_613_);
v___x_652_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_652_, 0, v_id_613_);
v___x_653_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_652_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_722_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_722_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_722_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_722_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
if (lean_obj_tag(v_a_654_) == 1)
{
lean_object* v_val_658_; 
v_val_658_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_val_658_);
lean_dec_ref(v_a_654_);
switch(lean_obj_tag(v_val_658_))
{
case 0:
{
lean_object* v_cat_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec(v_id_613_);
v_cat_659_ = lean_ctor_get(v_val_658_, 0);
lean_inc(v_cat_659_);
lean_dec_ref(v_val_658_);
v___x_660_ = lean_box(0);
v___x_661_ = l_Lean_Syntax_mkAntiquotNode(v_cat_659_, v_a_537_, v___x_585_, v___x_660_, v___x_545_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_661_);
v___x_663_ = v___x_656_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
case 1:
{
lean_object* v_decl_665_; 
lean_del_object(v___x_656_);
lean_dec(v_id_613_);
v_decl_665_ = lean_ctor_get(v_val_658_, 0);
lean_inc(v_decl_665_);
lean_dec_ref(v_val_658_);
if (lean_obj_tag(v_decl_665_) == 1)
{
lean_object* v_pre_666_; 
v_pre_666_ = lean_ctor_get(v_decl_665_, 0);
if (lean_obj_tag(v_pre_666_) == 1)
{
lean_object* v_pre_667_; 
v_pre_667_ = lean_ctor_get(v_pre_666_, 0);
if (lean_obj_tag(v_pre_667_) == 1)
{
lean_object* v_pre_668_; 
v_pre_668_ = lean_ctor_get(v_pre_667_, 0);
switch(lean_obj_tag(v_pre_668_))
{
case 0:
{
lean_object* v_str_669_; lean_object* v_str_670_; lean_object* v_str_671_; uint8_t v___x_672_; 
v_str_669_ = lean_ctor_get(v_decl_665_, 1);
v_str_670_ = lean_ctor_get(v_pre_666_, 1);
v_str_671_ = lean_ctor_get(v_pre_667_, 1);
v___x_672_ = lean_string_dec_eq(v_str_671_, v___x_541_);
if (v___x_672_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_string_dec_eq(v_str_670_, v___x_542_);
if (v___x_673_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = lean_string_dec_eq(v_str_669_, v___x_614_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_676_ = lean_string_dec_eq(v_str_669_, v___x_675_);
if (v___x_676_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
lean_object* v___x_677_; 
lean_dec_ref(v_decl_665_);
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_597_ = v___x_677_;
goto v___jp_596_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_decl_665_);
v___x_678_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_597_ = v___x_678_;
goto v___jp_596_;
}
}
}
}
case 1:
{
lean_object* v_pre_679_; 
v_pre_679_ = lean_ctor_get(v_pre_668_, 0);
if (lean_obj_tag(v_pre_679_) == 0)
{
lean_object* v_str_680_; lean_object* v_str_681_; lean_object* v_str_682_; lean_object* v_str_683_; uint8_t v___x_684_; 
v_str_680_ = lean_ctor_get(v_decl_665_, 1);
v_str_681_ = lean_ctor_get(v_pre_666_, 1);
v_str_682_ = lean_ctor_get(v_pre_667_, 1);
v_str_683_ = lean_ctor_get(v_pre_668_, 1);
v___x_684_ = lean_string_dec_eq(v_str_683_, v___x_541_);
if (v___x_684_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_string_dec_eq(v_str_682_, v___x_542_);
if (v___x_685_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_687_ = lean_string_dec_eq(v_str_681_, v___x_686_);
if (v___x_687_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = lean_string_dec_eq(v_str_680_, v___x_614_);
if (v___x_688_ == 0)
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
else
{
lean_object* v___x_689_; 
lean_dec_ref(v_decl_665_);
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_597_ = v___x_689_;
goto v___jp_596_;
}
}
}
}
}
else
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
}
default: 
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
}
}
else
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
}
else
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
}
else
{
v___y_597_ = v_decl_665_;
goto v___jp_596_;
}
}
default: 
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_656_);
v_isSharedCheck_714_ = !lean_is_exclusive(v_val_658_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_val_658_, 0);
lean_dec(v_unused_715_);
v___x_691_ = v_val_658_;
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_val_658_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_TSyntax_getId(v_id_613_);
lean_dec(v_id_613_);
v___x_694_ = lean_erase_macro_scopes(v___x_693_);
v___x_695_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_694_);
lean_dec(v___x_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; 
lean_del_object(v___x_691_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
if (lean_obj_tag(v_a_696_) == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
v___y_603_ = v___x_697_;
goto v___jp_602_;
}
else
{
lean_object* v_val_698_; 
v_val_698_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v_a_696_);
v___y_603_ = v_val_698_;
goto v___jp_602_;
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_537_);
v_a_699_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_713_ == 0)
{
v___x_701_ = v___x_695_;
v_isShared_702_ = v_isSharedCheck_713_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_713_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_ref_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v_ref_703_ = lean_ctor_get(v___y_650_, 7);
v___x_704_ = lean_io_error_to_string(v_a_699_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 3);
lean_ctor_set(v___x_691_, 0, v___x_704_);
v___x_706_ = v___x_691_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_712_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = l_Lean_MessageData_ofFormat(v___x_706_);
lean_inc(v_ref_703_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_ref_703_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_708_);
v___x_710_ = v___x_701_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
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
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_del_object(v___x_656_);
lean_dec(v_a_654_);
lean_dec(v_a_537_);
v___x_716_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_717_ = l_Lean_MessageData_ofSyntax(v_id_613_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_720_, v___y_650_, v___y_651_);
return v___x_721_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_id_613_);
lean_dec(v_a_537_);
v_a_723_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_653_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_653_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
v___jp_732_:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_array_get_size(v_a_733_);
v___x_735_ = lean_nat_dec_eq(v___x_734_, v___x_731_);
if (v___x_735_ == 0)
{
lean_dec_ref(v_a_733_);
goto v___jp_586_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = lean_array_fget(v_a_733_, v___x_585_);
lean_dec_ref(v_a_733_);
v_a_536_ = v___x_736_;
goto _start;
}
}
v___jp_738_:
{
if (lean_obj_tag(v___y_739_) == 0)
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v___y_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref(v___y_739_);
v_a_733_ = v_a_740_;
goto v___jp_732_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_537_);
v_a_741_ = lean_ctor_get(v___y_739_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___y_739_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___y_739_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___y_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_a_750_);
v___x_752_ = lean_nat_dec_eq(v___x_751_, v___x_731_);
if (v___x_752_ == 0)
{
lean_dec_ref(v_a_750_);
goto v___jp_591_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_array_fget(v_a_750_, v___x_585_);
lean_dec_ref(v_a_750_);
v_a_536_ = v___x_753_;
goto _start;
}
}
v___jp_755_:
{
if (lean_obj_tag(v___y_756_) == 0)
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___y_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___y_756_);
v_a_750_ = v_a_757_;
goto v___jp_749_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_537_);
v_a_758_ = lean_ctor_get(v___y_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___y_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___y_756_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___y_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
v___jp_586_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_box(0);
v___x_588_ = lean_box(0);
v___x_589_ = l_Lean_Syntax_mkAntiquotNode(v___x_587_, v_a_537_, v___x_585_, v___x_588_, v___x_545_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
v___jp_591_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_box(0);
v___x_593_ = lean_box(0);
v___x_594_ = l_Lean_Syntax_mkAntiquotNode(v___x_592_, v_a_537_, v___x_585_, v___x_593_, v___x_545_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
v___jp_596_:
{
lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_box(0);
v___x_599_ = 0;
v___x_600_ = l_Lean_Syntax_mkAntiquotNode(v___y_597_, v_a_537_, v___x_585_, v___x_598_, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
v___jp_602_:
{
lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = lean_box(0);
v___x_605_ = 0;
v___x_606_ = l_Lean_Syntax_mkAntiquotNode(v___y_603_, v_a_537_, v___x_585_, v___x_604_, v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
v___jp_608_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_box(0);
v___x_611_ = l_Lean_Syntax_mkAntiquotNode(v___x_609_, v_a_537_, v___x_585_, v___x_610_, v___x_545_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
v___jp_546_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = lean_box(0);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_box(0);
v___x_550_ = l_Lean_Syntax_mkAntiquotNode(v___x_547_, v_a_537_, v___x_548_, v___x_549_, v___x_545_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_804_, v___y_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_814_, lean_object* v_msg_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_820_, lean_object* v_msg_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_820_, v_msg_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_826_, lean_object* v_macroStack_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_826_, v_macroStack_827_, v___y_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_832_, lean_object* v_macroStack_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_832_, v_macroStack_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_841_, lean_object* v_stx_842_, lean_object* v_id_843_, lean_object* v_suffix_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_842_, v_id_843_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_863_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_863_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_863_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_863_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_853_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_841_, v_a_849_, v_suffix_844_);
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_mk_empty_array_with_capacity(v___x_854_);
v___x_856_ = lean_array_push(v___x_855_, v___x_853_);
v___x_857_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_858_ = lean_box(2);
v___x_859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_857_);
lean_ctor_set(v___x_859_, 2, v___x_856_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_859_);
v___x_861_ = v___x_851_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_dec_ref(v_suffix_844_);
lean_dec(v_kind_841_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_864_, lean_object* v_stx_865_, lean_object* v_id_866_, lean_object* v_suffix_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_864_, v_stx_865_, v_id_866_, v_suffix_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; lean_object* v_env_875_; lean_object* v___x_876_; lean_object* v_mainModule_877_; lean_object* v___x_878_; 
v___x_874_ = lean_st_ref_get(v___y_872_);
v_env_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_env_875_);
lean_dec(v___x_874_);
v___x_876_ = l_Lean_Environment_header(v_env_875_);
lean_dec_ref(v_env_875_);
v_mainModule_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_mainModule_877_);
lean_dec_ref(v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_mainModule_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_879_);
lean_dec(v___y_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_893_ = lean_panic_fn_borrowed(v___x_892_, v_msg_891_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Lean_maxRecDepthErrorMessage;
v___x_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_902_ = l_Lean_MessageData_ofFormat(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_904_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_905_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_906_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_ref_906_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_914_, lean_object* v_declName_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
uint8_t v___x_918_; lean_object* v_env_919_; lean_object* v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; 
v___x_918_ = 0;
v_env_919_ = l_Lean_Environment_setExporting(v_env_914_, v___x_918_);
lean_inc(v_declName_915_);
v___x_920_ = l_Lean_mkPrivateName(v_env_919_, v_declName_915_);
v___x_921_ = 1;
lean_inc_ref(v_env_919_);
v___x_922_ = l_Lean_Environment_contains(v_env_919_, v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = l_Lean_privateToUserName(v_declName_915_);
v___x_924_ = l_Lean_Environment_contains(v_env_919_, v___x_923_, v___x_921_);
v___x_925_ = lean_box(v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___y_917_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec_ref(v_env_919_);
lean_dec(v_declName_915_);
v___x_927_ = lean_box(v___x_922_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___y_917_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_929_, lean_object* v_declName_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_929_, v_declName_930_, v___y_931_, v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_933_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_934_, lean_object* v_i_935_, lean_object* v_k_936_){
_start:
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_array_get_size(v_keys_934_);
v___x_938_ = lean_nat_dec_lt(v_i_935_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec(v_i_935_);
return v___x_938_;
}
else
{
lean_object* v_k_x27_939_; uint8_t v___x_940_; 
v_k_x27_939_ = lean_array_fget_borrowed(v_keys_934_, v_i_935_);
v___x_940_ = l_Lean_instBEqExtraModUse_beq(v_k_936_, v_k_x27_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_add(v_i_935_, v___x_941_);
lean_dec(v_i_935_);
v_i_935_ = v___x_942_;
goto _start;
}
else
{
lean_dec(v_i_935_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_944_, lean_object* v_i_945_, lean_object* v_k_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_944_, v_i_945_, v_k_946_);
lean_dec_ref(v_k_946_);
lean_dec_ref(v_keys_944_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__0(void){
_start:
{
size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; 
v___x_949_ = ((size_t)5ULL);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_shift_left(v___x_950_, v___x_949_);
return v___x_951_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__1(void){
_start:
{
size_t v___x_952_; size_t v___x_953_; size_t v___x_954_; 
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__0);
v___x_954_ = lean_usize_sub(v___x_953_, v___x_952_);
return v___x_954_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_955_, size_t v_x_956_, lean_object* v_x_957_){
_start:
{
if (lean_obj_tag(v_x_955_) == 0)
{
lean_object* v_es_958_; lean_object* v___x_959_; size_t v___x_960_; size_t v___x_961_; size_t v___x_962_; lean_object* v_j_963_; lean_object* v___x_964_; 
v_es_958_ = lean_ctor_get(v_x_955_, 0);
v___x_959_ = lean_box(2);
v___x_960_ = ((size_t)5ULL);
v___x_961_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___closed__1);
v___x_962_ = lean_usize_land(v_x_956_, v___x_961_);
v_j_963_ = lean_usize_to_nat(v___x_962_);
v___x_964_ = lean_array_get_borrowed(v___x_959_, v_es_958_, v_j_963_);
lean_dec(v_j_963_);
switch(lean_obj_tag(v___x_964_))
{
case 0:
{
lean_object* v_key_965_; uint8_t v___x_966_; 
v_key_965_ = lean_ctor_get(v___x_964_, 0);
v___x_966_ = l_Lean_instBEqExtraModUse_beq(v_x_957_, v_key_965_);
return v___x_966_;
}
case 1:
{
lean_object* v_node_967_; size_t v___x_968_; 
v_node_967_ = lean_ctor_get(v___x_964_, 0);
v___x_968_ = lean_usize_shift_right(v_x_956_, v___x_960_);
v_x_955_ = v_node_967_;
v_x_956_ = v___x_968_;
goto _start;
}
default: 
{
uint8_t v___x_970_; 
v___x_970_ = 0;
return v___x_970_;
}
}
}
else
{
lean_object* v_ks_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_ks_971_ = lean_ctor_get(v_x_955_, 0);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_971_, v___x_972_, v_x_957_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
size_t v_x_84804__boxed_977_; uint8_t v_res_978_; lean_object* v_r_979_; 
v_x_84804__boxed_977_ = lean_unbox_usize(v_x_975_);
lean_dec(v_x_975_);
v_res_978_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_974_, v_x_84804__boxed_977_, v_x_976_);
lean_dec_ref(v_x_976_);
lean_dec_ref(v_x_974_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
uint64_t v___x_982_; size_t v___x_983_; uint8_t v___x_984_; 
v___x_982_ = l_Lean_instHashableExtraModUse_hash(v_x_981_);
v___x_983_ = lean_uint64_to_usize(v___x_982_);
v___x_984_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_980_, v___x_983_, v_x_981_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_985_, v_x_986_);
lean_dec_ref(v_x_986_);
lean_dec_ref(v_x_985_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_989_; double v___x_990_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_float_of_nat(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_993_, lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Elab_Command_getRef___redArg(v___y_995_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1047_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
v___x_1000_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_994_, v___y_996_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1047_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1047_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v_traceState_1006_; lean_object* v_env_1007_; lean_object* v_messages_1008_; lean_object* v_scopes_1009_; lean_object* v_usedQuotCtxts_1010_; lean_object* v_nextMacroScope_1011_; lean_object* v_maxRecDepth_1012_; lean_object* v_ngen_1013_; lean_object* v_auxDeclNGen_1014_; lean_object* v_infoState_1015_; lean_object* v_snapshotTasks_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1046_; 
v___x_1005_ = lean_st_ref_take(v___y_996_);
v_traceState_1006_ = lean_ctor_get(v___x_1005_, 9);
v_env_1007_ = lean_ctor_get(v___x_1005_, 0);
v_messages_1008_ = lean_ctor_get(v___x_1005_, 1);
v_scopes_1009_ = lean_ctor_get(v___x_1005_, 2);
v_usedQuotCtxts_1010_ = lean_ctor_get(v___x_1005_, 3);
v_nextMacroScope_1011_ = lean_ctor_get(v___x_1005_, 4);
v_maxRecDepth_1012_ = lean_ctor_get(v___x_1005_, 5);
v_ngen_1013_ = lean_ctor_get(v___x_1005_, 6);
v_auxDeclNGen_1014_ = lean_ctor_get(v___x_1005_, 7);
v_infoState_1015_ = lean_ctor_get(v___x_1005_, 8);
v_snapshotTasks_1016_ = lean_ctor_get(v___x_1005_, 10);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1018_ = v___x_1005_;
v_isShared_1019_ = v_isSharedCheck_1046_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snapshotTasks_1016_);
lean_inc(v_traceState_1006_);
lean_inc(v_infoState_1015_);
lean_inc(v_auxDeclNGen_1014_);
lean_inc(v_ngen_1013_);
lean_inc(v_maxRecDepth_1012_);
lean_inc(v_nextMacroScope_1011_);
lean_inc(v_usedQuotCtxts_1010_);
lean_inc(v_scopes_1009_);
lean_inc(v_messages_1008_);
lean_inc(v_env_1007_);
lean_dec(v___x_1005_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1046_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint64_t v_tid_1020_; lean_object* v_traces_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1045_; 
v_tid_1020_ = lean_ctor_get_uint64(v_traceState_1006_, sizeof(void*)*1);
v_traces_1021_ = lean_ctor_get(v_traceState_1006_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_traceState_1006_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1023_ = v_traceState_1006_;
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_traces_1021_);
lean_dec(v_traceState_1006_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; double v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_1027_ = 0;
v___x_1028_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1029_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1029_, 0, v_cls_993_);
lean_ctor_set(v___x_1029_, 1, v___x_1025_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
lean_ctor_set_float(v___x_1029_, sizeof(void*)*3, v___x_1026_);
lean_ctor_set_float(v___x_1029_, sizeof(void*)*3 + 8, v___x_1026_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*3 + 16, v___x_1027_);
v___x_1030_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_1031_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v_a_1001_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_a_999_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_PersistentArray_push___redArg(v_traces_1021_, v___x_1032_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1033_);
v___x_1035_ = v___x_1023_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1033_);
lean_ctor_set_uint64(v_reuseFailAlloc_1044_, sizeof(void*)*1, v_tid_1020_);
v___x_1035_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 9, v___x_1035_);
v___x_1037_ = v___x_1018_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_env_1007_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_messages_1008_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_scopes_1009_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_usedQuotCtxts_1010_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_nextMacroScope_1011_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v_maxRecDepth_1012_);
lean_ctor_set(v_reuseFailAlloc_1043_, 6, v_ngen_1013_);
lean_ctor_set(v_reuseFailAlloc_1043_, 7, v_auxDeclNGen_1014_);
lean_ctor_set(v_reuseFailAlloc_1043_, 8, v_infoState_1015_);
lean_ctor_set(v_reuseFailAlloc_1043_, 9, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1043_, 10, v_snapshotTasks_1016_);
v___x_1037_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = lean_st_ref_set(v___y_996_, v___x_1037_);
v___x_1039_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1039_);
v___x_1041_ = v___x_1003_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v_msg_994_);
lean_dec(v_cls_993_);
v_a_1048_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_998_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_998_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1056_, v_msg_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1061_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1));
v___x_1065_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0));
v___x_1066_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1065_, v___x_1064_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v_cls_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_cls_1079_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4));
v___x_1080_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1081_ = l_Lean_Name_append(v___x_1080_, v_cls_1079_);
return v___x_1081_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1092_, uint8_t v_isMeta_1093_, lean_object* v_hint_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; lean_object* v_env_1099_; uint8_t v_isExporting_1100_; lean_object* v___x_1101_; lean_object* v_env_1102_; lean_object* v___x_1103_; lean_object* v_entry_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___y_1109_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1098_ = lean_st_ref_get(v___y_1096_);
v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_env_1099_);
lean_dec(v___x_1098_);
v_isExporting_1100_ = lean_ctor_get_uint8(v_env_1099_, sizeof(void*)*8);
lean_dec_ref(v_env_1099_);
v___x_1101_ = lean_st_ref_get(v___y_1096_);
v_env_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1101_);
v___x_1103_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2);
lean_inc(v_mod_1092_);
v_entry_1104_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1104_, 0, v_mod_1092_);
lean_ctor_set_uint8(v_entry_1104_, sizeof(void*)*1, v_isExporting_1100_);
lean_ctor_set_uint8(v_entry_1104_, sizeof(void*)*1 + 1, v_isMeta_1093_);
v___x_1105_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1106_ = lean_box(1);
v___x_1107_ = lean_box(0);
v___x_1135_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1103_, v___x_1105_, v_env_1102_, v___x_1106_, v___x_1107_);
v___x_1136_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1135_, v_entry_1104_);
lean_dec(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_scopes_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_opts_1143_; uint8_t v_hasTrace_1144_; 
v___x_1137_ = l_Lean_inheritedTraceOptions;
v___x_1138_ = lean_st_ref_get(v___x_1137_);
v___x_1139_ = lean_st_ref_get(v___y_1096_);
v_scopes_1140_ = lean_ctor_get(v___x_1139_, 2);
lean_inc(v_scopes_1140_);
lean_dec(v___x_1139_);
v___x_1141_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1142_ = l_List_head_x21___redArg(v___x_1141_, v_scopes_1140_);
lean_dec(v_scopes_1140_);
v_opts_1143_ = lean_ctor_get(v___x_1142_, 1);
lean_inc_ref(v_opts_1143_);
lean_dec(v___x_1142_);
v_hasTrace_1144_ = lean_ctor_get_uint8(v_opts_1143_, sizeof(void*)*1);
if (v_hasTrace_1144_ == 0)
{
lean_dec_ref(v_opts_1143_);
lean_dec(v___x_1138_);
lean_dec(v_hint_1094_);
lean_dec(v_mod_1092_);
v___y_1109_ = v___y_1096_;
goto v___jp_1108_;
}
else
{
lean_object* v_cls_1145_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_cls_1145_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4));
v___x_1166_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
v___x_1167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1138_, v_opts_1143_, v___x_1166_);
lean_dec_ref(v_opts_1143_);
lean_dec(v___x_1138_);
if (v___x_1167_ == 0)
{
lean_dec(v_hint_1094_);
lean_dec(v_mod_1092_);
v___y_1109_ = v___y_1096_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1168_; lean_object* v___y_1170_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
if (v_isExporting_1100_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__18));
v___y_1170_ = v___x_1177_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__19));
v___y_1170_ = v___x_1178_;
goto v___jp_1169_;
}
v___jp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc_ref(v___y_1170_);
v___x_1171_ = l_Lean_stringToMessageData(v___y_1170_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1168_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
if (v_isMeta_1093_ == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1152_ = v___x_1174_;
v___y_1153_ = v___x_1175_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1152_ = v___x_1174_;
v___y_1153_ = v___x_1176_;
goto v___jp_1151_;
}
}
}
v___jp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___y_1147_);
lean_ctor_set(v___x_1149_, 1, v___y_1148_);
v___x_1150_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1145_, v___x_1149_, v___y_1095_, v___y_1096_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_dec_ref(v___x_1150_);
v___y_1109_ = v___y_1096_;
goto v___jp_1108_;
}
else
{
lean_dec_ref(v_entry_1104_);
return v___x_1150_;
}
}
v___jp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
lean_inc_ref(v___y_1153_);
v___x_1154_ = l_Lean_stringToMessageData(v___y_1153_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___y_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_ofName(v_mod_1092_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_Name_isAnonymous(v_hint_1094_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8);
v___x_1162_ = l_Lean_MessageData_ofName(v_hint_1094_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___y_1147_ = v___x_1159_;
v___y_1148_ = v___x_1163_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v_hint_1094_);
v___x_1164_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
v___y_1147_ = v___x_1159_;
v___y_1148_ = v___x_1165_;
goto v___jp_1146_;
}
}
}
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_entry_1104_);
lean_dec(v_hint_1094_);
lean_dec(v_mod_1092_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
v___jp_1108_:
{
lean_object* v___x_1110_; lean_object* v_toEnvExtension_1111_; lean_object* v_env_1112_; lean_object* v_messages_1113_; lean_object* v_scopes_1114_; lean_object* v_usedQuotCtxts_1115_; lean_object* v_nextMacroScope_1116_; lean_object* v_maxRecDepth_1117_; lean_object* v_ngen_1118_; lean_object* v_auxDeclNGen_1119_; lean_object* v_infoState_1120_; lean_object* v_traceState_1121_; lean_object* v_snapshotTasks_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1134_; 
v___x_1110_ = lean_st_ref_take(v___y_1109_);
v_toEnvExtension_1111_ = lean_ctor_get(v___x_1105_, 0);
v_env_1112_ = lean_ctor_get(v___x_1110_, 0);
v_messages_1113_ = lean_ctor_get(v___x_1110_, 1);
v_scopes_1114_ = lean_ctor_get(v___x_1110_, 2);
v_usedQuotCtxts_1115_ = lean_ctor_get(v___x_1110_, 3);
v_nextMacroScope_1116_ = lean_ctor_get(v___x_1110_, 4);
v_maxRecDepth_1117_ = lean_ctor_get(v___x_1110_, 5);
v_ngen_1118_ = lean_ctor_get(v___x_1110_, 6);
v_auxDeclNGen_1119_ = lean_ctor_get(v___x_1110_, 7);
v_infoState_1120_ = lean_ctor_get(v___x_1110_, 8);
v_traceState_1121_ = lean_ctor_get(v___x_1110_, 9);
v_snapshotTasks_1122_ = lean_ctor_get(v___x_1110_, 10);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1124_ = v___x_1110_;
v_isShared_1125_ = v_isSharedCheck_1134_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snapshotTasks_1122_);
lean_inc(v_traceState_1121_);
lean_inc(v_infoState_1120_);
lean_inc(v_auxDeclNGen_1119_);
lean_inc(v_ngen_1118_);
lean_inc(v_maxRecDepth_1117_);
lean_inc(v_nextMacroScope_1116_);
lean_inc(v_usedQuotCtxts_1115_);
lean_inc(v_scopes_1114_);
lean_inc(v_messages_1113_);
lean_inc(v_env_1112_);
lean_dec(v___x_1110_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1134_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_asyncMode_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v_asyncMode_1126_ = lean_ctor_get(v_toEnvExtension_1111_, 2);
v___x_1127_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1105_, v_env_1112_, v_entry_1104_, v_asyncMode_1126_, v___x_1107_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_messages_1113_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_scopes_1114_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_usedQuotCtxts_1115_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_nextMacroScope_1116_);
lean_ctor_set(v_reuseFailAlloc_1133_, 5, v_maxRecDepth_1117_);
lean_ctor_set(v_reuseFailAlloc_1133_, 6, v_ngen_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 7, v_auxDeclNGen_1119_);
lean_ctor_set(v_reuseFailAlloc_1133_, 8, v_infoState_1120_);
lean_ctor_set(v_reuseFailAlloc_1133_, 9, v_traceState_1121_);
lean_ctor_set(v_reuseFailAlloc_1133_, 10, v_snapshotTasks_1122_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_st_ref_set(v___y_1109_, v___x_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1181_, lean_object* v_isMeta_1182_, lean_object* v_hint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_isMeta_boxed_1187_; lean_object* v_res_1188_; 
v_isMeta_boxed_1187_ = lean_unbox(v_isMeta_1182_);
v_res_1188_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1181_, v_isMeta_boxed_1187_, v_hint_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1189_, lean_object* v_declName_1190_, lean_object* v_as_1191_, size_t v_sz_1192_, size_t v_i_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_usize_dec_lt(v_i_1193_, v_sz_1192_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v_declName_1190_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_b_1194_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v_modules_1201_; lean_object* v___x_1202_; lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v_toImport_1205_; lean_object* v_module_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1200_ = l_Lean_Environment_header(v___x_1189_);
v_modules_1201_ = lean_ctor_get(v___x_1200_, 3);
lean_inc_ref(v_modules_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1203_ = lean_array_uget_borrowed(v_as_1191_, v_i_1193_);
v___x_1204_ = lean_array_get(v___x_1202_, v_modules_1201_, v_a_1203_);
lean_dec_ref(v_modules_1201_);
v_toImport_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_ref(v_toImport_1205_);
lean_dec(v___x_1204_);
v_module_1206_ = lean_ctor_get(v_toImport_1205_, 0);
lean_inc(v_module_1206_);
lean_dec_ref(v_toImport_1205_);
v___x_1207_ = 0;
lean_inc(v_declName_1190_);
v___x_1208_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1206_, v___x_1207_, v_declName_1190_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; 
lean_dec_ref(v___x_1208_);
v___x_1209_ = lean_box(0);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_i_1193_, v___x_1210_);
v_i_1193_ = v___x_1211_;
v_b_1194_ = v___x_1209_;
goto _start;
}
else
{
lean_dec(v_declName_1190_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1213_, lean_object* v_declName_1214_, lean_object* v_as_1215_, lean_object* v_sz_1216_, lean_object* v_i_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
size_t v_sz_boxed_1222_; size_t v_i_boxed_1223_; lean_object* v_res_1224_; 
v_sz_boxed_1222_ = lean_unbox_usize(v_sz_1216_);
lean_dec(v_sz_1216_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1213_, v_declName_1214_, v_as_1215_, v_sz_boxed_1222_, v_i_boxed_1223_, v_b_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_as_1215_);
lean_dec_ref(v___x_1213_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1225_, lean_object* v_x_1226_){
_start:
{
if (lean_obj_tag(v_x_1226_) == 0)
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_box(0);
return v___x_1227_;
}
else
{
lean_object* v_key_1228_; lean_object* v_value_1229_; lean_object* v_tail_1230_; uint8_t v___x_1231_; 
v_key_1228_ = lean_ctor_get(v_x_1226_, 0);
v_value_1229_ = lean_ctor_get(v_x_1226_, 1);
v_tail_1230_ = lean_ctor_get(v_x_1226_, 2);
v___x_1231_ = lean_name_eq(v_key_1228_, v_a_1225_);
if (v___x_1231_ == 0)
{
v_x_1226_ = v_tail_1230_;
goto _start;
}
else
{
lean_object* v___x_1233_; 
lean_inc(v_value_1229_);
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_value_1229_);
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1234_, lean_object* v_x_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1234_, v_x_1235_);
lean_dec(v_x_1235_);
lean_dec(v_a_1234_);
return v_res_1236_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1237_; uint64_t v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(1723u);
v___x_1238_ = lean_uint64_of_nat(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_buckets_1241_; lean_object* v___x_1242_; uint64_t v___y_1244_; 
v_buckets_1241_ = lean_ctor_get(v_m_1239_, 1);
v___x_1242_ = lean_array_get_size(v_buckets_1241_);
if (lean_obj_tag(v_a_1240_) == 0)
{
uint64_t v___x_1258_; 
v___x_1258_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0);
v___y_1244_ = v___x_1258_;
goto v___jp_1243_;
}
else
{
uint64_t v_hash_1259_; 
v_hash_1259_ = lean_ctor_get_uint64(v_a_1240_, sizeof(void*)*2);
v___y_1244_ = v_hash_1259_;
goto v___jp_1243_;
}
v___jp_1243_:
{
uint64_t v___x_1245_; uint64_t v___x_1246_; uint64_t v_fold_1247_; uint64_t v___x_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1245_ = 32ULL;
v___x_1246_ = lean_uint64_shift_right(v___y_1244_, v___x_1245_);
v_fold_1247_ = lean_uint64_xor(v___y_1244_, v___x_1246_);
v___x_1248_ = 16ULL;
v___x_1249_ = lean_uint64_shift_right(v_fold_1247_, v___x_1248_);
v___x_1250_ = lean_uint64_xor(v_fold_1247_, v___x_1249_);
v___x_1251_ = lean_uint64_to_usize(v___x_1250_);
v___x_1252_ = lean_usize_of_nat(v___x_1242_);
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = lean_usize_sub(v___x_1252_, v___x_1253_);
v___x_1255_ = lean_usize_land(v___x_1251_, v___x_1254_);
v___x_1256_ = lean_array_uget_borrowed(v_buckets_1241_, v___x_1255_);
v___x_1257_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1240_, v___x_1256_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_m_1260_);
return v_res_1262_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___x_1266_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0));
v___x_1267_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1270_, uint8_t v_isMeta_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v_env_1279_; lean_object* v___y_1281_; lean_object* v___x_1294_; 
v___x_1275_ = lean_st_ref_get(v___y_1273_);
v_env_1279_ = lean_ctor_get(v___x_1275_, 0);
lean_inc_ref(v_env_1279_);
lean_dec(v___x_1275_);
v___x_1294_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1279_, v_declName_1270_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_dec_ref(v_env_1279_);
lean_dec(v_declName_1270_);
goto v___jp_1276_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1296_; lean_object* v_modules_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_val_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1295_);
lean_dec_ref(v___x_1294_);
v___x_1296_ = l_Lean_Environment_header(v_env_1279_);
v_modules_1297_ = lean_ctor_get(v___x_1296_, 3);
lean_inc_ref(v_modules_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = lean_array_get_size(v_modules_1297_);
v___x_1299_ = lean_nat_dec_lt(v_val_1295_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v_modules_1297_);
lean_dec(v_val_1295_);
lean_dec_ref(v_env_1279_);
lean_dec(v_declName_1270_);
goto v___jp_1276_;
}
else
{
lean_object* v___x_1300_; lean_object* v_env_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___y_1305_; 
v___x_1300_ = lean_st_ref_get(v___y_1273_);
v_env_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc_ref(v_env_1301_);
lean_dec(v___x_1300_);
v___x_1302_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2);
v___x_1303_ = lean_array_fget(v_modules_1297_, v_val_1295_);
lean_dec(v_val_1295_);
lean_dec_ref(v_modules_1297_);
if (v_isMeta_1271_ == 0)
{
lean_dec_ref(v_env_1301_);
v___y_1305_ = v_isMeta_1271_;
goto v___jp_1304_;
}
else
{
uint8_t v___x_1316_; 
lean_inc(v_declName_1270_);
v___x_1316_ = l_Lean_isMarkedMeta(v_env_1301_, v_declName_1270_);
if (v___x_1316_ == 0)
{
v___y_1305_ = v_isMeta_1271_;
goto v___jp_1304_;
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = 0;
v___y_1305_ = v___x_1317_;
goto v___jp_1304_;
}
}
v___jp_1304_:
{
lean_object* v_toImport_1306_; lean_object* v_module_1307_; lean_object* v___x_1308_; 
v_toImport_1306_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_ref(v_toImport_1306_);
lean_dec(v___x_1303_);
v_module_1307_ = lean_ctor_get(v_toImport_1306_, 0);
lean_inc(v_module_1307_);
lean_dec_ref(v_toImport_1306_);
lean_inc(v_declName_1270_);
v___x_1308_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1307_, v___y_1305_, v_declName_1270_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v___x_1308_);
v___x_1309_ = l_Lean_indirectModUseExt;
v___x_1310_ = lean_box(1);
v___x_1311_ = lean_box(0);
lean_inc_ref(v_env_1279_);
v___x_1312_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1302_, v___x_1309_, v_env_1279_, v___x_1310_, v___x_1311_);
v___x_1313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1312_, v_declName_1270_);
lean_dec(v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__3));
v___y_1281_ = v___x_1314_;
goto v___jp_1280_;
}
else
{
lean_object* v_val_1315_; 
v_val_1315_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1315_);
lean_dec_ref(v___x_1313_);
v___y_1281_ = v_val_1315_;
goto v___jp_1280_;
}
}
else
{
lean_dec_ref(v_env_1279_);
lean_dec(v_declName_1270_);
return v___x_1308_;
}
}
}
}
v___jp_1276_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
v___jp_1280_:
{
lean_object* v___x_1282_; size_t v_sz_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_box(0);
v_sz_1283_ = lean_array_size(v___y_1281_);
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1279_, v_declName_1270_, v___y_1281_, v_sz_1283_, v___x_1284_, v___x_1282_, v___y_1272_, v___y_1273_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v_env_1279_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1293_);
v___x_1287_ = v___x_1285_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1282_);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1282_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1318_, lean_object* v_isMeta_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v_isMeta_boxed_1323_; lean_object* v_res_1324_; 
v_isMeta_boxed_1323_ = lean_unbox(v_isMeta_1319_);
v_res_1324_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1318_, v_isMeta_boxed_1323_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
if (lean_obj_tag(v_as_x27_1325_) == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_b_1326_);
return v___x_1330_;
}
else
{
lean_object* v_head_1331_; lean_object* v_tail_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; 
v_head_1331_ = lean_ctor_get(v_as_x27_1325_, 0);
lean_inc(v_head_1331_);
v_tail_1332_ = lean_ctor_get(v_as_x27_1325_, 1);
lean_inc(v_tail_1332_);
lean_dec_ref(v_as_x27_1325_);
v___x_1333_ = 1;
v___x_1334_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1331_, v___x_1333_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref(v___x_1334_);
v___x_1335_ = lean_box(0);
v_as_x27_1325_ = v_tail_1332_;
v_b_1326_ = v___x_1335_;
goto _start;
}
else
{
lean_dec(v_tail_1332_);
return v___x_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1337_, v_b_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1343_, lean_object* v_opts_1344_, lean_object* v_currNamespace_1345_, lean_object* v_openDecls_1346_, lean_object* v_n_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = l_Lean_ResolveName_resolveGlobalName(v_env_1343_, v_opts_1344_, v_currNamespace_1345_, v_openDecls_1346_, v_n_1347_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___y_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1352_, lean_object* v_opts_1353_, lean_object* v_currNamespace_1354_, lean_object* v_openDecls_1355_, lean_object* v_n_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1352_, v_opts_1353_, v_currNamespace_1354_, v_openDecls_1355_, v_n_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v_opts_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Elab_Command_getRef___redArg(v___y_1362_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v_fileName_1367_; lean_object* v_fileMap_1368_; lean_object* v_currRecDepth_1369_; lean_object* v_cmdPos_1370_; lean_object* v_macroStack_1371_; lean_object* v_quotContext_x3f_1372_; lean_object* v_currMacroScope_1373_; lean_object* v_snap_x3f_1374_; lean_object* v_cancelTk_x3f_1375_; uint8_t v_suppressElabErrors_1376_; lean_object* v_ref_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v_fileName_1367_ = lean_ctor_get(v___y_1362_, 0);
v_fileMap_1368_ = lean_ctor_get(v___y_1362_, 1);
v_currRecDepth_1369_ = lean_ctor_get(v___y_1362_, 2);
v_cmdPos_1370_ = lean_ctor_get(v___y_1362_, 3);
v_macroStack_1371_ = lean_ctor_get(v___y_1362_, 4);
v_quotContext_x3f_1372_ = lean_ctor_get(v___y_1362_, 5);
v_currMacroScope_1373_ = lean_ctor_get(v___y_1362_, 6);
v_snap_x3f_1374_ = lean_ctor_get(v___y_1362_, 8);
v_cancelTk_x3f_1375_ = lean_ctor_get(v___y_1362_, 9);
v_suppressElabErrors_1376_ = lean_ctor_get_uint8(v___y_1362_, sizeof(void*)*10);
v_ref_1377_ = l_Lean_replaceRef(v_ref_1360_, v_a_1366_);
lean_dec(v_a_1366_);
lean_inc(v_cancelTk_x3f_1375_);
lean_inc(v_snap_x3f_1374_);
lean_inc(v_currMacroScope_1373_);
lean_inc(v_quotContext_x3f_1372_);
lean_inc(v_macroStack_1371_);
lean_inc(v_cmdPos_1370_);
lean_inc(v_currRecDepth_1369_);
lean_inc_ref(v_fileMap_1368_);
lean_inc_ref(v_fileName_1367_);
v___x_1378_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1378_, 0, v_fileName_1367_);
lean_ctor_set(v___x_1378_, 1, v_fileMap_1368_);
lean_ctor_set(v___x_1378_, 2, v_currRecDepth_1369_);
lean_ctor_set(v___x_1378_, 3, v_cmdPos_1370_);
lean_ctor_set(v___x_1378_, 4, v_macroStack_1371_);
lean_ctor_set(v___x_1378_, 5, v_quotContext_x3f_1372_);
lean_ctor_set(v___x_1378_, 6, v_currMacroScope_1373_);
lean_ctor_set(v___x_1378_, 7, v_ref_1377_);
lean_ctor_set(v___x_1378_, 8, v_snap_x3f_1374_);
lean_ctor_set(v___x_1378_, 9, v_cancelTk_x3f_1375_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*10, v_suppressElabErrors_1376_);
v___x_1379_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1361_, v___x_1378_, v___y_1363_);
lean_dec_ref(v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v_msg_1361_);
v_a_1380_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1365_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1365_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1388_, v_msg_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v_ref_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1394_, lean_object* v_currNamespace_1395_, lean_object* v_openDecls_1396_, lean_object* v_n_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = l_Lean_ResolveName_resolveNamespace(v_env_1394_, v_currNamespace_1395_, v_openDecls_1396_, v_n_1397_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1402_, lean_object* v_currNamespace_1403_, lean_object* v_openDecls_1404_, lean_object* v_n_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1402_, v_currNamespace_1403_, v_openDecls_1404_, v_n_1405_, v___y_1406_, v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_currNamespace_1409_);
lean_ctor_set(v___x_1412_, 1, v___y_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1413_, v___y_1414_, v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1417_, lean_object* v___y_1418_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_a_1419_);
v___x_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_a_1419_);
lean_ctor_set(v___x_1420_, 1, v___y_1418_);
return v___x_1420_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_a_1421_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_a_1421_);
lean_ctor_set(v___x_1422_, 1, v___y_1418_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1423_, v___y_1424_);
lean_dec_ref(v_x_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1426_, lean_object* v_stx_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1426_, v_stx_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
if (lean_obj_tag(v_a_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v___x_1430_, 0);
lean_dec(v_unused_1441_);
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_box(0);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_a_1432_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1470_; 
v_val_1442_ = lean_ctor_get(v_a_1431_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1444_ = v_a_1431_;
v_isShared_1445_ = v_isSharedCheck_1470_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_val_1442_);
lean_dec(v_a_1431_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1470_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_snd_1446_; 
v_snd_1446_ = lean_ctor_get(v_val_1442_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_val_1442_);
if (lean_obj_tag(v_snd_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
lean_del_object(v___x_1444_);
v_a_1447_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1430_);
v_a_1448_ = lean_ctor_get(v_snd_1446_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_snd_1446_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1450_ = v_snd_1446_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v_snd_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1453_, v_a_1447_);
lean_dec_ref(v___x_1453_);
return v___x_1454_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1469_; 
v_a_1457_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1430_);
v_a_1458_ = lean_ctor_get(v_snd_1446_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_snd_1446_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1460_ = v_snd_1446_;
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v_snd_1446_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_a_1458_);
v___x_1463_ = v___x_1444_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1465_, v_a_1457_);
lean_dec_ref(v___x_1465_);
return v___x_1466_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1471_ = lean_ctor_get(v___x_1430_, 0);
v_a_1472_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1430_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_inc(v_a_1471_);
lean_dec(v___x_1430_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1471_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1480_, lean_object* v_stx_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1480_, v_stx_1481_, v___y_1482_, v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
if (lean_obj_tag(v_as_1493_) == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
else
{
lean_object* v_head_1499_; lean_object* v_tail_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_scopes_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v_opts_1509_; uint8_t v_hasTrace_1510_; 
v_head_1499_ = lean_ctor_get(v_as_1493_, 0);
lean_inc(v_head_1499_);
v_tail_1500_ = lean_ctor_get(v_as_1493_, 1);
lean_inc(v_tail_1500_);
lean_dec_ref(v_as_1493_);
v_fst_1501_ = lean_ctor_get(v_head_1499_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v_head_1499_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_head_1499_);
v___x_1503_ = l_Lean_inheritedTraceOptions;
v___x_1504_ = lean_st_ref_get(v___x_1503_);
v___x_1505_ = lean_st_ref_get(v___y_1495_);
v_scopes_1506_ = lean_ctor_get(v___x_1505_, 2);
lean_inc(v_scopes_1506_);
lean_dec(v___x_1505_);
v___x_1507_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1508_ = l_List_head_x21___redArg(v___x_1507_, v_scopes_1506_);
lean_dec(v_scopes_1506_);
v_opts_1509_ = lean_ctor_get(v___x_1508_, 1);
lean_inc_ref(v_opts_1509_);
lean_dec(v___x_1508_);
v_hasTrace_1510_ = lean_ctor_get_uint8(v_opts_1509_, sizeof(void*)*1);
if (v_hasTrace_1510_ == 0)
{
lean_dec_ref(v_opts_1509_);
lean_dec(v___x_1504_);
lean_dec(v_snd_1502_);
lean_dec(v_fst_1501_);
v_as_1493_ = v_tail_1500_;
goto _start;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
lean_inc(v_fst_1501_);
v___x_1513_ = l_Lean_Name_append(v___x_1512_, v_fst_1501_);
v___x_1514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1504_, v_opts_1509_, v___x_1513_);
lean_dec(v___x_1513_);
lean_dec_ref(v_opts_1509_);
lean_dec(v___x_1504_);
if (v___x_1514_ == 0)
{
lean_dec(v_snd_1502_);
lean_dec(v_fst_1501_);
v_as_1493_ = v_tail_1500_;
goto _start;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_snd_1502_);
v___x_1517_ = l_Lean_MessageData_ofFormat(v___x_1516_);
v___x_1518_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1501_, v___x_1517_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_dec_ref(v___x_1518_);
v_as_1493_ = v_tail_1500_;
goto _start;
}
else
{
lean_dec(v_tail_1500_);
return v___x_1518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v_env_1531_; lean_object* v___x_1532_; lean_object* v_scopes_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_opts_1536_; lean_object* v___x_1537_; 
v___x_1530_ = lean_st_ref_get(v___y_1528_);
v_env_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc_ref(v_env_1531_);
lean_dec(v___x_1530_);
v___x_1532_ = lean_st_ref_get(v___y_1528_);
v_scopes_1533_ = lean_ctor_get(v___x_1532_, 2);
lean_inc(v_scopes_1533_);
lean_dec(v___x_1532_);
v___x_1534_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1535_ = l_List_head_x21___redArg(v___x_1534_, v_scopes_1533_);
lean_dec(v_scopes_1533_);
v_opts_1536_ = lean_ctor_get(v___x_1535_, 1);
lean_inc_ref(v_opts_1536_);
lean_dec(v___x_1535_);
v___x_1537_ = l_Lean_Elab_Command_getScope___redArg(v___y_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_currNamespace_1539_; lean_object* v___x_1540_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v___x_1537_);
v_currNamespace_1539_ = lean_ctor_get(v_a_1538_, 2);
lean_inc(v_currNamespace_1539_);
lean_dec(v_a_1538_);
v___x_1540_ = l_Lean_Elab_Command_getScope___redArg(v___y_1528_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v_openDecls_1542_; lean_object* v___x_1543_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v_openDecls_1542_ = lean_ctor_get(v_a_1541_, 3);
lean_inc(v_openDecls_1542_);
lean_dec(v_a_1541_);
v___x_1543_ = l_Lean_Elab_Command_getRef___redArg(v___y_1527_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1527_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_currRecDepth_1547_; lean_object* v_quotContext_x3f_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v_methods_1554_; lean_object* v_a_1556_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v_currRecDepth_1547_ = lean_ctor_get(v___y_1527_, 2);
v_quotContext_x3f_1548_ = lean_ctor_get(v___y_1527_, 5);
lean_inc_ref_n(v_env_1531_, 3);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1549_, 0, v_env_1531_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1550_, 0, v_env_1531_);
lean_inc_n(v_currNamespace_1539_, 2);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1551_, 0, v_currNamespace_1539_);
lean_inc(v_openDecls_1542_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1552_, 0, v_env_1531_);
lean_closure_set(v___f_1552_, 1, v_currNamespace_1539_);
lean_closure_set(v___f_1552_, 2, v_openDecls_1542_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1553_, 0, v_env_1531_);
lean_closure_set(v___f_1553_, 1, v_opts_1536_);
lean_closure_set(v___f_1553_, 2, v_currNamespace_1539_);
lean_closure_set(v___f_1553_, 3, v_openDecls_1542_);
v_methods_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1554_, 0, v___f_1550_);
lean_ctor_set(v_methods_1554_, 1, v___f_1551_);
lean_ctor_set(v_methods_1554_, 2, v___f_1549_);
lean_ctor_set(v_methods_1554_, 3, v___f_1552_);
lean_ctor_set(v_methods_1554_, 4, v___f_1553_);
if (lean_obj_tag(v_quotContext_x3f_1548_) == 0)
{
lean_object* v___x_1628_; lean_object* v_a_1629_; 
v___x_1628_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1528_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref(v___x_1628_);
v_a_1556_ = v_a_1629_;
goto v___jp_1555_;
}
else
{
lean_object* v_val_1630_; 
v_val_1630_ = lean_ctor_get(v_quotContext_x3f_1548_, 0);
lean_inc(v_val_1630_);
v_a_1556_ = v_val_1630_;
goto v___jp_1555_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v_maxRecDepth_1558_; lean_object* v___x_1559_; lean_object* v_nextMacroScope_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1557_ = lean_st_ref_get(v___y_1528_);
v_maxRecDepth_1558_ = lean_ctor_get(v___x_1557_, 5);
lean_inc(v_maxRecDepth_1558_);
lean_dec(v___x_1557_);
v___x_1559_ = lean_st_ref_get(v___y_1528_);
v_nextMacroScope_1560_ = lean_ctor_get(v___x_1559_, 4);
lean_inc(v_nextMacroScope_1560_);
lean_dec(v___x_1559_);
lean_inc(v_currRecDepth_1547_);
v___x_1561_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1561_, 0, v_methods_1554_);
lean_ctor_set(v___x_1561_, 1, v_a_1556_);
lean_ctor_set(v___x_1561_, 2, v_a_1546_);
lean_ctor_set(v___x_1561_, 3, v_currRecDepth_1547_);
lean_ctor_set(v___x_1561_, 4, v_maxRecDepth_1558_);
lean_ctor_set(v___x_1561_, 5, v_a_1544_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1563_, 0, v_nextMacroScope_1560_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_ctor_set(v___x_1563_, 2, v___x_1562_);
v___x_1564_ = lean_apply_2(v_x_1526_, v___x_1561_, v___x_1563_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v_a_1566_; lean_object* v_macroScope_1567_; lean_object* v_traceMsgs_1568_; lean_object* v_expandedMacroDecls_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_a_1565_);
v_a_1566_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1564_);
v_macroScope_1567_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_macroScope_1567_);
v_traceMsgs_1568_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_traceMsgs_1568_);
v_expandedMacroDecls_1569_ = lean_ctor_get(v_a_1565_, 2);
lean_inc(v_expandedMacroDecls_1569_);
lean_dec(v_a_1565_);
v___x_1570_ = lean_box(0);
v___x_1571_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1569_, v___x_1570_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; lean_object* v_env_1573_; lean_object* v_messages_1574_; lean_object* v_scopes_1575_; lean_object* v_usedQuotCtxts_1576_; lean_object* v_maxRecDepth_1577_; lean_object* v_ngen_1578_; lean_object* v_auxDeclNGen_1579_; lean_object* v_infoState_1580_; lean_object* v_traceState_1581_; lean_object* v_snapshotTasks_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v___x_1571_);
v___x_1572_ = lean_st_ref_take(v___y_1528_);
v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
v_messages_1574_ = lean_ctor_get(v___x_1572_, 1);
v_scopes_1575_ = lean_ctor_get(v___x_1572_, 2);
v_usedQuotCtxts_1576_ = lean_ctor_get(v___x_1572_, 3);
v_maxRecDepth_1577_ = lean_ctor_get(v___x_1572_, 5);
v_ngen_1578_ = lean_ctor_get(v___x_1572_, 6);
v_auxDeclNGen_1579_ = lean_ctor_get(v___x_1572_, 7);
v_infoState_1580_ = lean_ctor_get(v___x_1572_, 8);
v_traceState_1581_ = lean_ctor_get(v___x_1572_, 9);
v_snapshotTasks_1582_ = lean_ctor_get(v___x_1572_, 10);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1572_, 4);
lean_dec(v_unused_1609_);
v___x_1584_ = v___x_1572_;
v_isShared_1585_ = v_isSharedCheck_1608_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snapshotTasks_1582_);
lean_inc(v_traceState_1581_);
lean_inc(v_infoState_1580_);
lean_inc(v_auxDeclNGen_1579_);
lean_inc(v_ngen_1578_);
lean_inc(v_maxRecDepth_1577_);
lean_inc(v_usedQuotCtxts_1576_);
lean_inc(v_scopes_1575_);
lean_inc(v_messages_1574_);
lean_inc(v_env_1573_);
lean_dec(v___x_1572_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1608_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v_macroScope_1567_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_env_1573_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_messages_1574_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_scopes_1575_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_usedQuotCtxts_1576_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_macroScope_1567_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v_maxRecDepth_1577_);
lean_ctor_set(v_reuseFailAlloc_1607_, 6, v_ngen_1578_);
lean_ctor_set(v_reuseFailAlloc_1607_, 7, v_auxDeclNGen_1579_);
lean_ctor_set(v_reuseFailAlloc_1607_, 8, v_infoState_1580_);
lean_ctor_set(v_reuseFailAlloc_1607_, 9, v_traceState_1581_);
lean_ctor_set(v_reuseFailAlloc_1607_, 10, v_snapshotTasks_1582_);
v___x_1587_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_st_ref_set(v___y_1528_, v___x_1587_);
v___x_1589_ = l_List_reverse___redArg(v_traceMsgs_1568_);
v___x_1590_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1589_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v___x_1590_, 0);
lean_dec(v_unused_1598_);
v___x_1592_ = v___x_1590_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v___x_1590_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_a_1566_);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1566_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1566_);
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1590_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1590_);
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
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_traceMsgs_1568_);
lean_dec(v_macroScope_1567_);
lean_dec(v_a_1566_);
v_a_1610_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1571_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1571_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; 
v_a_1618_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1564_);
if (lean_obj_tag(v_a_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v_a_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_a_1619_ = lean_ctor_get(v_a_1618_, 0);
lean_inc(v_a_1619_);
v_a_1620_ = lean_ctor_get(v_a_1618_, 1);
lean_inc_ref(v_a_1620_);
lean_dec_ref(v_a_1618_);
v___x_1621_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1622_ = lean_string_dec_eq(v_a_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_a_1620_);
v___x_1624_ = l_Lean_MessageData_ofFormat(v___x_1623_);
v___x_1625_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1619_, v___x_1624_, v___y_1527_, v___y_1528_);
lean_dec(v_a_1619_);
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; 
lean_dec_ref(v_a_1620_);
v___x_1626_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1619_);
return v___x_1626_;
}
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_a_1544_);
lean_dec(v_openDecls_1542_);
lean_dec(v_currNamespace_1539_);
lean_dec_ref(v_opts_1536_);
lean_dec_ref(v_env_1531_);
lean_dec_ref(v_x_1526_);
v_a_1631_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1545_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1545_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_openDecls_1542_);
lean_dec(v_currNamespace_1539_);
lean_dec_ref(v_opts_1536_);
lean_dec_ref(v_env_1531_);
lean_dec_ref(v_x_1526_);
v_a_1639_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1543_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1543_);
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
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_currNamespace_1539_);
lean_dec_ref(v_opts_1536_);
lean_dec_ref(v_env_1531_);
lean_dec_ref(v_x_1526_);
v_a_1647_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1540_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1540_);
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
lean_dec_ref(v_opts_1536_);
lean_dec_ref(v_env_1531_);
lean_dec_ref(v_x_1526_);
v_a_1655_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1537_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1537_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1667_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1682_ = l_String_toRawSubstring_x27(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1706_ = lean_unsigned_to_nat(14u);
v___x_1707_ = lean_unsigned_to_nat(22u);
v___x_1708_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1709_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1710_ = l_mkPanicMessageWithDecl(v___x_1709_, v___x_1708_, v___x_1707_, v___x_1706_, v___x_1705_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1727_ = l_String_toRawSubstring_x27(v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1740_ = l_Lean_mkAtom(v___x_1739_);
return v___x_1740_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1743_ = l_Lean_mkAtom(v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1744_, lean_object* v_id_1745_, lean_object* v_stx_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_pat_1751_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1746_);
v___x_1755_ = l_Lean_Syntax_isOfKind(v_stx_1746_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1746_);
v___x_1757_ = l_Lean_Syntax_isOfKind(v_stx_1746_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v_a_1764_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v_a_1800_; uint8_t v___x_1831_; 
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1746_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v_stx_1746_, v___x_1758_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1746_);
v___x_1833_ = l_Lean_Syntax_isOfKind(v_stx_1746_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1746_);
v___x_1835_ = l_Lean_Syntax_isOfKind(v_stx_1746_, v___x_1834_);
if (v___x_1835_ == 0)
{
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_quotContext_x3f_1840_; lean_object* v___x_1841_; lean_object* v_a_1843_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1838_);
v_quotContext_x3f_1840_ = lean_ctor_get(v_a_1747_, 5);
v___x_1841_ = l_Lean_SourceInfo_fromRef(v_a_1837_, v___x_1835_);
lean_dec(v_a_1837_);
if (lean_obj_tag(v_quotContext_x3f_1840_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
v_a_1843_ = v_a_1875_;
goto v___jp_1842_;
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v___x_1841_);
lean_dec(v_a_1839_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_1876_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1874_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_val_1884_; 
v_val_1884_ = lean_ctor_get(v_quotContext_x3f_1840_, 0);
lean_inc(v_val_1884_);
v_a_1843_ = v_val_1884_;
goto v___jp_1842_;
}
v___jp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1844_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1845_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1846_ = l_Lean_addMacroScope(v_a_1843_, v___x_1845_, v_a_1839_);
v___x_1847_ = lean_box(0);
lean_inc_n(v___x_1841_, 3);
v___x_1848_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1841_);
lean_ctor_set(v___x_1848_, 1, v___x_1844_);
lean_ctor_set(v___x_1848_, 2, v___x_1846_);
lean_ctor_set(v___x_1848_, 3, v___x_1847_);
v___x_1849_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1841_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_1852_ = l_Lean_Syntax_node1(v___x_1841_, v___x_1851_, v_stx_1746_);
v___x_1853_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1865_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1865_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1865_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1858_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1841_);
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1841_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_Syntax_node4(v___x_1841_, v___x_1758_, v___x_1848_, v___x_1850_, v___x_1852_, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1861_);
v___x_1863_ = v___x_1856_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v___x_1852_);
lean_dec_ref(v___x_1850_);
lean_dec_ref(v___x_1848_);
lean_dec(v___x_1841_);
v_a_1866_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1853_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1853_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1837_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_1885_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1838_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1838_);
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
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_1893_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1836_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1836_);
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
lean_object* v_val_1901_; lean_object* v___x_1902_; 
lean_dec(v_id_1745_);
v_val_1901_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_1901_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_1902_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_1901_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v_pat_1751_ = v_a_1903_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_stx_1746_);
v_a_1904_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1902_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1902_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_1912_);
lean_inc(v___x_1913_);
v___x_1914_ = l_Lean_Syntax_matchesNull(v___x_1913_, v___x_1912_);
if (v___x_1914_ == 0)
{
lean_dec(v___x_1913_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_quotContext_x3f_1919_; lean_object* v___x_1920_; lean_object* v_a_1922_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
v_quotContext_x3f_1919_ = lean_ctor_get(v_a_1747_, 5);
v___x_1920_ = l_Lean_SourceInfo_fromRef(v_a_1916_, v___x_1914_);
lean_dec(v_a_1916_);
if (lean_obj_tag(v_quotContext_x3f_1919_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1953_);
v_a_1922_ = v_a_1954_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v___x_1920_);
lean_dec(v_a_1918_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_1955_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1953_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1953_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v_quotContext_x3f_1919_, 0);
lean_inc(v_val_1963_);
v_a_1922_ = v_val_1963_;
goto v___jp_1921_;
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1925_ = l_Lean_addMacroScope(v_a_1922_, v___x_1924_, v_a_1918_);
v___x_1926_ = lean_box(0);
lean_inc_n(v___x_1920_, 3);
v___x_1927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1920_);
lean_ctor_set(v___x_1927_, 1, v___x_1923_);
lean_ctor_set(v___x_1927_, 2, v___x_1925_);
lean_ctor_set(v___x_1927_, 3, v___x_1926_);
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1920_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_1931_ = l_Lean_Syntax_node1(v___x_1920_, v___x_1930_, v_stx_1746_);
v___x_1932_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1944_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1944_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1944_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1937_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1920_);
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1920_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_Syntax_node4(v___x_1920_, v___x_1758_, v___x_1927_, v___x_1929_, v___x_1931_, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_a_1933_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1940_);
v___x_1942_ = v___x_1935_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v___x_1931_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v___x_1927_);
lean_dec(v___x_1920_);
v_a_1945_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1932_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1932_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_a_1916_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_1964_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1917_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1917_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
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
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_1972_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1915_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1915_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1981_; 
lean_dec(v_id_1745_);
v_val_1980_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_1980_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_1981_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_1980_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1981_);
v_pat_1751_ = v_a_1982_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_stx_1746_);
v_a_1983_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
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
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1991_ = lean_unsigned_to_nat(3u);
v___x_1992_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_1991_);
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_1992_);
v___x_1994_ = l_Lean_Syntax_isOfKind(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec(v___x_1992_);
lean_dec(v___x_1913_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1995_);
v___x_1997_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v_quotContext_x3f_1999_; lean_object* v___x_2000_; lean_object* v_a_2002_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1997_);
v_quotContext_x3f_1999_ = lean_ctor_get(v_a_1747_, 5);
v___x_2000_ = l_Lean_SourceInfo_fromRef(v_a_1996_, v___x_1994_);
lean_dec(v_a_1996_);
if (lean_obj_tag(v_quotContext_x3f_1999_) == 0)
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v_a_2002_ = v_a_2034_;
goto v___jp_2001_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v___x_2000_);
lean_dec(v_a_1998_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2035_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2033_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2033_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_val_2043_; 
v_val_2043_ = lean_ctor_get(v_quotContext_x3f_1999_, 0);
lean_inc(v_val_2043_);
v_a_2002_ = v_val_2043_;
goto v___jp_2001_;
}
v___jp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2003_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2004_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2005_ = l_Lean_addMacroScope(v_a_2002_, v___x_2004_, v_a_1998_);
v___x_2006_ = lean_box(0);
lean_inc_n(v___x_2000_, 3);
v___x_2007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2000_);
lean_ctor_set(v___x_2007_, 1, v___x_2003_);
lean_ctor_set(v___x_2007_, 2, v___x_2005_);
lean_ctor_set(v___x_2007_, 3, v___x_2006_);
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2000_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2011_ = l_Lean_Syntax_node1(v___x_2000_, v___x_2010_, v_stx_1746_);
v___x_2012_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2024_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2024_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2024_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2000_);
v___x_2018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2000_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = l_Lean_Syntax_node4(v___x_2000_, v___x_1758_, v___x_2007_, v___x_2009_, v___x_2011_, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_a_2013_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2020_);
v___x_2022_ = v___x_2015_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v___x_2011_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2007_);
lean_dec(v___x_2000_);
v_a_2025_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2012_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2012_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_1996_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2044_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_1997_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_1997_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2052_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1995_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1995_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_val_2060_; lean_object* v___x_2061_; 
lean_dec(v_id_1745_);
v_val_2060_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2060_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2061_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2060_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2061_);
v_pat_1751_ = v_a_2062_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_stx_1746_);
v_a_2063_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2061_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2061_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v_stx_2072_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___x_2098_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2071_ = lean_unsigned_to_nat(0u);
v_stx_2072_ = l_Lean_Syntax_getArg(v___x_1913_, v___x_2071_);
lean_dec(v___x_1913_);
v___x_2098_ = lean_unsigned_to_nat(2u);
v___x_2150_ = lean_unsigned_to_nat(4u);
v___x_2151_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2150_);
v___x_2152_ = l_Lean_Syntax_isNone(v___x_2151_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; 
lean_inc(v___x_2151_);
v___x_2153_ = l_Lean_Syntax_matchesNull(v___x_2151_, v___x_2098_);
if (v___x_2153_ == 0)
{
lean_dec(v___x_2151_);
lean_dec(v_stx_2072_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v_quotContext_x3f_2158_; lean_object* v___x_2159_; lean_object* v_a_2161_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
v_quotContext_x3f_2158_ = lean_ctor_get(v_a_1747_, 5);
v___x_2159_ = l_Lean_SourceInfo_fromRef(v_a_2155_, v___x_1833_);
lean_dec(v_a_2155_);
if (lean_obj_tag(v_quotContext_x3f_2158_) == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
v_a_2161_ = v_a_2193_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v___x_2159_);
lean_dec(v_a_2157_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2194_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2192_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_val_2202_; 
v_val_2202_ = lean_ctor_get(v_quotContext_x3f_2158_, 0);
lean_inc(v_val_2202_);
v_a_2161_ = v_val_2202_;
goto v___jp_2160_;
}
v___jp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2162_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2164_ = l_Lean_addMacroScope(v_a_2161_, v___x_2163_, v_a_2157_);
v___x_2165_ = lean_box(0);
lean_inc_n(v___x_2159_, 3);
v___x_2166_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2159_);
lean_ctor_set(v___x_2166_, 1, v___x_2162_);
lean_ctor_set(v___x_2166_, 2, v___x_2164_);
lean_ctor_set(v___x_2166_, 3, v___x_2165_);
v___x_2167_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2159_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2170_ = l_Lean_Syntax_node1(v___x_2159_, v___x_2169_, v_stx_1746_);
v___x_2171_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2183_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2183_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2183_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2159_);
v___x_2177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2159_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_Syntax_node4(v___x_2159_, v___x_1758_, v___x_2166_, v___x_2168_, v___x_2170_, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v_a_2172_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2179_);
v___x_2181_ = v___x_2174_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v___x_2170_);
lean_dec_ref(v___x_2168_);
lean_dec_ref(v___x_2166_);
lean_dec(v___x_2159_);
v_a_2184_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2171_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2171_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_a_2155_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2203_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2156_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2156_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2211_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2154_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2154_);
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
else
{
lean_object* v_val_2219_; lean_object* v___x_2220_; 
lean_dec(v_id_1745_);
v_val_2219_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2219_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2220_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2219_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
v_pat_1751_ = v_a_2221_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_stx_1746_);
v_a_2222_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = l_Lean_Syntax_getArg(v___x_2151_, v___x_1912_);
lean_dec(v___x_2151_);
v___x_2231_ = l_Lean_Syntax_matchesNull(v___x_2230_, v___x_1912_);
if (v___x_2231_ == 0)
{
lean_dec(v_stx_2072_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_quotContext_x3f_2236_; lean_object* v___x_2237_; lean_object* v_a_2239_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2234_);
v_quotContext_x3f_2236_ = lean_ctor_get(v_a_1747_, 5);
v___x_2237_ = l_Lean_SourceInfo_fromRef(v_a_2233_, v___x_1833_);
lean_dec(v_a_2233_);
if (lean_obj_tag(v_quotContext_x3f_2236_) == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2270_);
v_a_2239_ = v_a_2271_;
goto v___jp_2238_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v___x_2237_);
lean_dec(v_a_2235_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2272_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2270_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2270_);
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
else
{
lean_object* v_val_2280_; 
v_val_2280_ = lean_ctor_get(v_quotContext_x3f_2236_, 0);
lean_inc(v_val_2280_);
v_a_2239_ = v_val_2280_;
goto v___jp_2238_;
}
v___jp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2240_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2241_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2242_ = l_Lean_addMacroScope(v_a_2239_, v___x_2241_, v_a_2235_);
v___x_2243_ = lean_box(0);
lean_inc_n(v___x_2237_, 3);
v___x_2244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2237_);
lean_ctor_set(v___x_2244_, 1, v___x_2240_);
lean_ctor_set(v___x_2244_, 2, v___x_2242_);
lean_ctor_set(v___x_2244_, 3, v___x_2243_);
v___x_2245_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2237_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2248_ = l_Lean_Syntax_node1(v___x_2237_, v___x_2247_, v_stx_1746_);
v___x_2249_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2261_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2261_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2261_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2237_);
v___x_2255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2237_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_node4(v___x_2237_, v___x_1758_, v___x_2244_, v___x_2246_, v___x_2248_, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v_a_2250_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2257_);
v___x_2259_ = v___x_2252_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2244_);
lean_dec(v___x_2237_);
v_a_2262_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2249_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2249_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_a_2233_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2281_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2234_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2234_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2289_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2232_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2232_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_val_2297_; lean_object* v___x_2298_; 
lean_dec(v_id_1745_);
v_val_2297_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2297_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2298_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2297_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v_pat_1751_ = v_a_2299_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec(v_stx_1746_);
v_a_2300_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2298_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
v___y_2100_ = v_a_1747_;
v___y_2101_ = v_a_1748_;
goto v___jp_2099_;
}
}
}
else
{
lean_dec(v___x_2151_);
v___y_2100_ = v_a_1747_;
v___y_2101_ = v_a_1748_;
goto v___jp_2099_;
}
v___jp_2073_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2079_ = lean_string_append(v___y_2077_, v___x_2078_);
lean_inc(v___y_2076_);
v___x_2080_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2076_, v_stx_2072_, v_id_1745_, v___x_2079_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
v_pat_1751_ = v_a_2081_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_stx_1746_);
v_a_2082_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
v___jp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2094_ = l_Lean_Syntax_isStrLit_x3f(v___x_1992_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2096_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2095_);
v___y_2074_ = v___y_2091_;
v___y_2075_ = v___y_2092_;
v___y_2076_ = v___x_2093_;
v___y_2077_ = v___x_2096_;
goto v___jp_2073_;
}
else
{
lean_object* v_val_2097_; 
v_val_2097_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_val_2097_);
lean_dec_ref(v___x_2094_);
v___y_2074_ = v___y_2091_;
v___y_2075_ = v___y_2092_;
v___y_2076_ = v___x_2093_;
v___y_2077_ = v_val_2097_;
goto v___jp_2073_;
}
}
v___jp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = lean_unsigned_to_nat(5u);
v___x_2103_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2102_);
v___x_2104_ = l_Lean_Syntax_isNone(v___x_2103_);
if (v___x_2104_ == 0)
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_Syntax_matchesNull(v___x_2103_, v___x_2098_);
if (v___x_2105_ == 0)
{
lean_dec(v_stx_2072_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Elab_Command_getRef___redArg(v___y_2100_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2100_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_quotContext_x3f_2110_; lean_object* v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v_quotContext_x3f_2110_ = lean_ctor_get(v___y_2100_, 5);
v___x_2111_ = l_Lean_SourceInfo_fromRef(v_a_2107_, v___x_1833_);
lean_dec(v_a_2107_);
if (lean_obj_tag(v_quotContext_x3f_2110_) == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2101_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v___y_1760_ = v___y_2101_;
v___y_1761_ = v_a_2109_;
v___y_1762_ = v___x_2111_;
v___y_1763_ = v___y_2100_;
v_a_1764_ = v_a_2113_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v___x_2111_);
lean_dec(v_a_2109_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2114_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2112_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2112_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_val_2122_; 
v_val_2122_ = lean_ctor_get(v_quotContext_x3f_2110_, 0);
lean_inc(v_val_2122_);
v___y_1760_ = v___y_2101_;
v___y_1761_ = v_a_2109_;
v___y_1762_ = v___x_2111_;
v___y_1763_ = v___y_2100_;
v_a_1764_ = v_val_2122_;
goto v___jp_1759_;
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_a_2107_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2123_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2108_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2108_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2131_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2106_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2106_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2140_; 
lean_dec(v_id_1745_);
v_val_2139_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2139_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2140_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2139_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___x_2140_);
v_pat_1751_ = v_a_2141_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_stx_1746_);
v_a_2142_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2140_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2140_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1744_);
v___y_2091_ = v___y_2100_;
v___y_2092_ = v___y_2101_;
goto v___jp_2090_;
}
}
else
{
lean_dec(v___x_2103_);
lean_dec(v_id_x3f_1744_);
v___y_2091_ = v___y_2100_;
v___y_2092_ = v___y_2101_;
goto v___jp_2090_;
}
}
}
}
}
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = lean_unsigned_to_nat(1u);
v___x_2309_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2308_);
lean_inc(v___x_2309_);
v___x_2310_ = l_Lean_Syntax_matchesNull(v___x_2309_, v___x_2308_);
if (v___x_2310_ == 0)
{
lean_dec(v___x_2309_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v_quotContext_x3f_2315_; lean_object* v___x_2316_; lean_object* v_a_2318_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
v_quotContext_x3f_2315_ = lean_ctor_get(v_a_1747_, 5);
v___x_2316_ = l_Lean_SourceInfo_fromRef(v_a_2312_, v___x_2310_);
lean_dec(v_a_2312_);
if (lean_obj_tag(v_quotContext_x3f_2315_) == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v_a_2318_ = v_a_2350_;
goto v___jp_2317_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v___x_2316_);
lean_dec(v_a_2314_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2351_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2349_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v_val_2359_; 
v_val_2359_ = lean_ctor_get(v_quotContext_x3f_2315_, 0);
lean_inc(v_val_2359_);
v_a_2318_ = v_val_2359_;
goto v___jp_2317_;
}
v___jp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2319_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2320_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2321_ = l_Lean_addMacroScope(v_a_2318_, v___x_2320_, v_a_2314_);
v___x_2322_ = lean_box(0);
lean_inc_n(v___x_2316_, 3);
v___x_2323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2316_);
lean_ctor_set(v___x_2323_, 1, v___x_2319_);
lean_ctor_set(v___x_2323_, 2, v___x_2321_);
lean_ctor_set(v___x_2323_, 3, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2316_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2327_ = l_Lean_Syntax_node1(v___x_2316_, v___x_2326_, v_stx_1746_);
v___x_2328_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2340_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2316_);
v___x_2334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2316_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node4(v___x_2316_, v___x_1758_, v___x_2323_, v___x_2325_, v___x_2327_, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v_a_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2336_);
v___x_2338_ = v___x_2331_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v___x_2327_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v___x_2323_);
lean_dec(v___x_2316_);
v_a_2341_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2328_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2328_);
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
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2312_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2360_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2313_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2313_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2368_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2311_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2311_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_val_2376_; lean_object* v___x_2377_; 
lean_dec(v_id_1745_);
v_val_2376_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2376_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2377_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2376_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v_pat_1751_ = v_a_2378_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_stx_1746_);
v_a_2379_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2377_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2387_ = lean_unsigned_to_nat(3u);
v___x_2388_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2388_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v___x_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_dec(v___x_2388_);
lean_dec(v___x_2309_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v_quotContext_x3f_2395_; lean_object* v___x_2396_; lean_object* v_a_2398_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v_quotContext_x3f_2395_ = lean_ctor_get(v_a_1747_, 5);
v___x_2396_ = l_Lean_SourceInfo_fromRef(v_a_2392_, v___x_2390_);
lean_dec(v_a_2392_);
if (lean_obj_tag(v_quotContext_x3f_2395_) == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2429_);
v_a_2398_ = v_a_2430_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v___x_2396_);
lean_dec(v_a_2394_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2431_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2429_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2429_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_val_2439_; 
v_val_2439_ = lean_ctor_get(v_quotContext_x3f_2395_, 0);
lean_inc(v_val_2439_);
v_a_2398_ = v_val_2439_;
goto v___jp_2397_;
}
v___jp_2397_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2399_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2400_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2401_ = l_Lean_addMacroScope(v_a_2398_, v___x_2400_, v_a_2394_);
v___x_2402_ = lean_box(0);
lean_inc_n(v___x_2396_, 3);
v___x_2403_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2396_);
lean_ctor_set(v___x_2403_, 1, v___x_2399_);
lean_ctor_set(v___x_2403_, 2, v___x_2401_);
lean_ctor_set(v___x_2403_, 3, v___x_2402_);
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2396_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2407_ = l_Lean_Syntax_node1(v___x_2396_, v___x_2406_, v_stx_1746_);
v___x_2408_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2420_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2396_);
v___x_2414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2396_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_Syntax_node4(v___x_2396_, v___x_1758_, v___x_2403_, v___x_2405_, v___x_2407_, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v_a_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2416_);
v___x_2418_ = v___x_2411_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v___x_2407_);
lean_dec_ref(v___x_2405_);
lean_dec_ref(v___x_2403_);
lean_dec(v___x_2396_);
v_a_2421_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2408_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2408_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_a_2392_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2440_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2393_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2393_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2448_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2391_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2391_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v_val_2456_; lean_object* v___x_2457_; 
lean_dec(v_id_1745_);
v_val_2456_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2456_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2457_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2456_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v_pat_1751_ = v_a_2458_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_stx_1746_);
v_a_2459_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2457_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_object* v___x_2467_; lean_object* v_stx_2468_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v_stx_2468_ = l_Lean_Syntax_getArg(v___x_2309_, v___x_2467_);
lean_dec(v___x_2309_);
v___x_2494_ = lean_unsigned_to_nat(2u);
v___x_2546_ = lean_unsigned_to_nat(4u);
v___x_2547_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2546_);
v___x_2548_ = l_Lean_Syntax_isNone(v___x_2547_);
if (v___x_2548_ == 0)
{
uint8_t v___x_2549_; 
lean_inc(v___x_2547_);
v___x_2549_ = l_Lean_Syntax_matchesNull(v___x_2547_, v___x_2494_);
if (v___x_2549_ == 0)
{
lean_dec(v___x_2547_);
lean_dec(v_stx_2468_);
lean_dec(v___x_2388_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_quotContext_x3f_2554_; lean_object* v___x_2555_; lean_object* v_a_2557_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v_quotContext_x3f_2554_ = lean_ctor_get(v_a_1747_, 5);
v___x_2555_ = l_Lean_SourceInfo_fromRef(v_a_2551_, v___x_1831_);
lean_dec(v_a_2551_);
if (lean_obj_tag(v_quotContext_x3f_2554_) == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v_a_2557_ = v_a_2589_;
goto v___jp_2556_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___x_2555_);
lean_dec(v_a_2553_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2590_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2588_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2588_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_val_2598_; 
v_val_2598_ = lean_ctor_get(v_quotContext_x3f_2554_, 0);
lean_inc(v_val_2598_);
v_a_2557_ = v_val_2598_;
goto v___jp_2556_;
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2558_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2559_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2560_ = l_Lean_addMacroScope(v_a_2557_, v___x_2559_, v_a_2553_);
v___x_2561_ = lean_box(0);
lean_inc_n(v___x_2555_, 3);
v___x_2562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2555_);
lean_ctor_set(v___x_2562_, 1, v___x_2558_);
lean_ctor_set(v___x_2562_, 2, v___x_2560_);
lean_ctor_set(v___x_2562_, 3, v___x_2561_);
v___x_2563_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2555_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2566_ = l_Lean_Syntax_node1(v___x_2555_, v___x_2565_, v_stx_1746_);
v___x_2567_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2579_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2555_);
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2555_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node4(v___x_2555_, v___x_1758_, v___x_2562_, v___x_2564_, v___x_2566_, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_a_2568_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2575_);
v___x_2577_ = v___x_2570_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v___x_2566_);
lean_dec_ref(v___x_2564_);
lean_dec_ref(v___x_2562_);
lean_dec(v___x_2555_);
v_a_2580_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2567_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2567_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_a_2551_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2599_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2552_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2552_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2607_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2550_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2550_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_val_2615_; lean_object* v___x_2616_; 
lean_dec(v_id_1745_);
v_val_2615_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2615_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2616_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2615_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v___x_2616_);
v_pat_1751_ = v_a_2617_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v_stx_1746_);
v_a_2618_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2616_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
else
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = l_Lean_Syntax_getArg(v___x_2547_, v___x_2308_);
lean_dec(v___x_2547_);
v___x_2627_ = l_Lean_Syntax_matchesNull(v___x_2626_, v___x_2308_);
if (v___x_2627_ == 0)
{
lean_dec(v_stx_2468_);
lean_dec(v___x_2388_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
v___x_2630_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v_quotContext_x3f_2632_; lean_object* v___x_2633_; lean_object* v_a_2635_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
v_quotContext_x3f_2632_ = lean_ctor_get(v_a_1747_, 5);
v___x_2633_ = l_Lean_SourceInfo_fromRef(v_a_2629_, v___x_1831_);
lean_dec(v_a_2629_);
if (lean_obj_tag(v_quotContext_x3f_2632_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref(v___x_2666_);
v_a_2635_ = v_a_2667_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v___x_2633_);
lean_dec(v_a_2631_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2668_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2666_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_val_2676_; 
v_val_2676_ = lean_ctor_get(v_quotContext_x3f_2632_, 0);
lean_inc(v_val_2676_);
v_a_2635_ = v_val_2676_;
goto v___jp_2634_;
}
v___jp_2634_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2636_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2638_ = l_Lean_addMacroScope(v_a_2635_, v___x_2637_, v_a_2631_);
v___x_2639_ = lean_box(0);
lean_inc_n(v___x_2633_, 3);
v___x_2640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2633_);
lean_ctor_set(v___x_2640_, 1, v___x_2636_);
lean_ctor_set(v___x_2640_, 2, v___x_2638_);
lean_ctor_set(v___x_2640_, 3, v___x_2639_);
v___x_2641_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2633_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2644_ = l_Lean_Syntax_node1(v___x_2633_, v___x_2643_, v_stx_1746_);
v___x_2645_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2657_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2633_);
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2633_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_Syntax_node4(v___x_2633_, v___x_1758_, v___x_2640_, v___x_2642_, v___x_2644_, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2653_);
v___x_2655_ = v___x_2648_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v___x_2644_);
lean_dec_ref(v___x_2642_);
lean_dec_ref(v___x_2640_);
lean_dec(v___x_2633_);
v_a_2658_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2645_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_a_2629_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2677_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2630_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2630_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2685_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2628_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2628_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v_val_2693_; lean_object* v___x_2694_; 
lean_dec(v_id_1745_);
v_val_2693_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2693_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2694_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2693_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
v_pat_1751_ = v_a_2695_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_stx_1746_);
v_a_2696_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2694_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
else
{
v___y_2496_ = v_a_1747_;
v___y_2497_ = v_a_1748_;
goto v___jp_2495_;
}
}
}
else
{
lean_dec(v___x_2547_);
v___y_2496_ = v_a_1747_;
v___y_2497_ = v_a_1748_;
goto v___jp_2495_;
}
v___jp_2469_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2475_ = lean_string_append(v___y_2473_, v___x_2474_);
lean_inc(v___y_2471_);
v___x_2476_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2471_, v_stx_2468_, v_id_1745_, v___x_2475_, v___y_2472_, v___y_2470_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
v_pat_1751_ = v_a_2477_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_stx_1746_);
v_a_2478_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2476_);
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
}
v___jp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2490_ = l_Lean_Syntax_isStrLit_x3f(v___x_2388_);
lean_dec(v___x_2388_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2492_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2491_);
v___y_2470_ = v___y_2488_;
v___y_2471_ = v___x_2489_;
v___y_2472_ = v___y_2487_;
v___y_2473_ = v___x_2492_;
goto v___jp_2469_;
}
else
{
lean_object* v_val_2493_; 
v_val_2493_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_val_2493_);
lean_dec_ref(v___x_2490_);
v___y_2470_ = v___y_2488_;
v___y_2471_ = v___x_2489_;
v___y_2472_ = v___y_2487_;
v___y_2473_ = v_val_2493_;
goto v___jp_2469_;
}
}
v___jp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2498_ = lean_unsigned_to_nat(5u);
v___x_2499_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_isNone(v___x_2499_);
if (v___x_2500_ == 0)
{
uint8_t v___x_2501_; 
v___x_2501_ = l_Lean_Syntax_matchesNull(v___x_2499_, v___x_2494_);
if (v___x_2501_ == 0)
{
lean_dec(v_stx_2468_);
lean_dec(v___x_2388_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_Elab_Command_getRef___redArg(v___y_2496_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2496_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v_quotContext_x3f_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2504_);
v_quotContext_x3f_2506_ = lean_ctor_get(v___y_2496_, 5);
v___x_2507_ = l_Lean_SourceInfo_fromRef(v_a_2503_, v___x_1831_);
lean_dec(v_a_2503_);
if (lean_obj_tag(v_quotContext_x3f_2506_) == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2497_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v___x_2508_);
v___y_1796_ = v_a_2505_;
v___y_1797_ = v___x_2507_;
v___y_1798_ = v___y_2496_;
v___y_1799_ = v___y_2497_;
v_a_1800_ = v_a_2509_;
goto v___jp_1795_;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v___x_2507_);
lean_dec(v_a_2505_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2510_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2508_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v_val_2518_; 
v_val_2518_ = lean_ctor_get(v_quotContext_x3f_2506_, 0);
lean_inc(v_val_2518_);
v___y_1796_ = v_a_2505_;
v___y_1797_ = v___x_2507_;
v___y_1798_ = v___y_2496_;
v___y_1799_ = v___y_2497_;
v_a_1800_ = v_val_2518_;
goto v___jp_1795_;
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_a_2503_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2519_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2504_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2504_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2527_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2502_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2502_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2536_; 
lean_dec(v_id_1745_);
v_val_2535_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2535_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2536_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2535_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v_pat_1751_ = v_a_2537_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_stx_1746_);
v_a_2538_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1744_);
v___y_2487_ = v___y_2496_;
v___y_2488_ = v___y_2497_;
goto v___jp_2486_;
}
}
else
{
lean_dec(v___x_2499_);
lean_dec(v_id_x3f_1744_);
v___y_2487_ = v___y_2496_;
v___y_2488_ = v___y_2497_;
goto v___jp_2486_;
}
}
}
}
}
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2707_ = l_Lean_Syntax_matchesIdent(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2709_ = l_Lean_Syntax_matchesIdent(v___x_2705_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2711_ = l_Lean_Syntax_matchesIdent(v___x_2705_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2713_ = l_Lean_Syntax_matchesIdent(v___x_2705_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2715_ = l_Lean_Syntax_matchesIdent(v___x_2705_, v___x_2714_);
lean_dec(v___x_2705_);
if (v___x_2715_ == 0)
{
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref(v___x_2716_);
v___x_2718_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_quotContext_x3f_2720_; lean_object* v___x_2721_; lean_object* v_a_2723_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref(v___x_2718_);
v_quotContext_x3f_2720_ = lean_ctor_get(v_a_1747_, 5);
v___x_2721_ = l_Lean_SourceInfo_fromRef(v_a_2717_, v___x_2715_);
lean_dec(v_a_2717_);
if (lean_obj_tag(v_quotContext_x3f_2720_) == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v_a_2723_ = v_a_2755_;
goto v___jp_2722_;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v___x_2721_);
lean_dec(v_a_2719_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2756_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2754_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_val_2764_; 
v_val_2764_ = lean_ctor_get(v_quotContext_x3f_2720_, 0);
lean_inc(v_val_2764_);
v_a_2723_ = v_val_2764_;
goto v___jp_2722_;
}
v___jp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2724_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2725_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2726_ = l_Lean_addMacroScope(v_a_2723_, v___x_2725_, v_a_2719_);
v___x_2727_ = lean_box(0);
lean_inc_n(v___x_2721_, 3);
v___x_2728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2721_);
lean_ctor_set(v___x_2728_, 1, v___x_2724_);
lean_ctor_set(v___x_2728_, 2, v___x_2726_);
lean_ctor_set(v___x_2728_, 3, v___x_2727_);
v___x_2729_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2721_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2732_ = l_Lean_Syntax_node1(v___x_2721_, v___x_2731_, v_stx_1746_);
v___x_2733_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2745_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2721_);
v___x_2739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2721_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = l_Lean_Syntax_node4(v___x_2721_, v___x_1758_, v___x_2728_, v___x_2730_, v___x_2732_, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_a_2734_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2741_);
v___x_2743_ = v___x_2736_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec_ref(v___x_2728_);
lean_dec(v___x_2721_);
v_a_2746_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2733_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2733_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_a_2717_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2765_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2718_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2718_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2773_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2716_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2716_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_val_2781_; lean_object* v___x_2782_; 
lean_dec(v_id_1745_);
v_val_2781_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2781_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2782_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2781_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
v_pat_1751_ = v_a_2783_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_stx_1746_);
v_a_2784_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2782_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2782_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = lean_unsigned_to_nat(2u);
v___x_2794_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2793_);
lean_inc(v___x_2794_);
v___x_2795_ = l_Lean_Syntax_matchesNull(v___x_2794_, v___x_2792_);
if (v___x_2795_ == 0)
{
lean_dec(v___x_2794_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v___x_2798_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v_quotContext_x3f_2800_; lean_object* v___x_2801_; lean_object* v_a_2803_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2798_);
v_quotContext_x3f_2800_ = lean_ctor_get(v_a_1747_, 5);
v___x_2801_ = l_Lean_SourceInfo_fromRef(v_a_2797_, v___x_2795_);
lean_dec(v_a_2797_);
if (lean_obj_tag(v_quotContext_x3f_2800_) == 0)
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2834_);
v_a_2803_ = v_a_2835_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v___x_2801_);
lean_dec(v_a_2799_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2836_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2834_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2834_);
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
}
else
{
lean_object* v_val_2844_; 
v_val_2844_ = lean_ctor_get(v_quotContext_x3f_2800_, 0);
lean_inc(v_val_2844_);
v_a_2803_ = v_val_2844_;
goto v___jp_2802_;
}
v___jp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2804_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2805_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2806_ = l_Lean_addMacroScope(v_a_2803_, v___x_2805_, v_a_2799_);
v___x_2807_ = lean_box(0);
lean_inc_n(v___x_2801_, 3);
v___x_2808_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2801_);
lean_ctor_set(v___x_2808_, 1, v___x_2804_);
lean_ctor_set(v___x_2808_, 2, v___x_2806_);
lean_ctor_set(v___x_2808_, 3, v___x_2807_);
v___x_2809_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2801_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2812_ = l_Lean_Syntax_node1(v___x_2801_, v___x_2811_, v_stx_1746_);
v___x_2813_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2825_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2825_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2825_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2801_);
v___x_2819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2801_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = l_Lean_Syntax_node4(v___x_2801_, v___x_1758_, v___x_2808_, v___x_2810_, v___x_2812_, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v_a_2814_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2821_);
v___x_2823_ = v___x_2816_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___x_2812_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v___x_2808_);
lean_dec(v___x_2801_);
v_a_2826_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2813_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2813_);
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
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_a_2797_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2845_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2798_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2798_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2853_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2796_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2796_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v_val_2861_; lean_object* v___x_2862_; 
lean_dec(v_id_1745_);
v_val_2861_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_2861_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_2862_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_2861_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
v_pat_1751_ = v_a_2863_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_stx_1746_);
v_a_2864_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2862_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
else
{
lean_object* v_stx_2872_; lean_object* v___x_2873_; 
lean_dec(v_stx_1746_);
v_stx_2872_ = l_Lean_Syntax_getArg(v___x_2794_, v___x_2704_);
lean_dec(v___x_2794_);
v___x_2873_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1744_, v_id_1745_, v_stx_2872_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_fst_2875_; lean_object* v_snd_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2936_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
v_fst_2875_ = lean_ctor_get(v_a_2874_, 0);
v_snd_2876_ = lean_ctor_get(v_a_2874_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_a_2874_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2878_ = v_a_2874_;
v_isShared_2879_ = v_isSharedCheck_2936_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snd_2876_);
lean_inc(v_fst_2875_);
lean_dec(v_a_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2936_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2919_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2885_ = v___x_2882_;
v_isShared_2886_ = v_isSharedCheck_2919_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2919_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v_quotContext_x3f_2887_; lean_object* v___x_2888_; lean_object* v_a_2890_; 
v_quotContext_x3f_2887_ = lean_ctor_get(v_a_1747_, 5);
v___x_2888_ = l_Lean_SourceInfo_fromRef(v_a_2881_, v___x_2713_);
lean_dec(v_a_2881_);
if (lean_obj_tag(v_quotContext_x3f_2887_) == 0)
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v_a_2890_ = v_a_2909_;
goto v___jp_2889_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v___x_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2883_);
lean_del_object(v___x_2878_);
lean_dec(v_snd_2876_);
lean_dec(v_fst_2875_);
v_a_2910_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2908_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2908_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_val_2918_; 
v_val_2918_ = lean_ctor_get(v_quotContext_x3f_2887_, 0);
lean_inc(v_val_2918_);
v_a_2890_ = v_val_2918_;
goto v___jp_2889_;
}
v___jp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2891_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_2892_ = l_Lean_addMacroScope(v_a_2890_, v___x_2714_, v_a_2883_);
v___x_2893_ = lean_box(0);
lean_inc_n(v___x_2888_, 4);
v___x_2894_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2888_);
lean_ctor_set(v___x_2894_, 1, v___x_2891_);
lean_ctor_set(v___x_2894_, 2, v___x_2892_);
lean_ctor_set(v___x_2894_, 3, v___x_2893_);
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2888_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_2898_ = l_Lean_Syntax_node1(v___x_2888_, v___x_2897_, v_fst_2875_);
v___x_2899_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2888_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Lean_Syntax_node4(v___x_2888_, v___x_1758_, v___x_2894_, v___x_2896_, v___x_2898_, v___x_2900_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2901_);
v___x_2903_ = v___x_2878_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_snd_2876_);
v___x_2903_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2905_; 
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v___x_2903_);
v___x_2905_ = v___x_2885_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2881_);
lean_del_object(v___x_2878_);
lean_dec(v_snd_2876_);
lean_dec(v_fst_2875_);
v_a_2920_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2882_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2882_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_del_object(v___x_2878_);
lean_dec(v_snd_2876_);
lean_dec(v_fst_2875_);
v_a_2928_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2880_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2880_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
else
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
lean_dec(v___x_2705_);
v___x_2937_ = lean_unsigned_to_nat(1u);
v___x_2938_ = lean_unsigned_to_nat(2u);
v___x_2939_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_2938_);
lean_inc(v___x_2939_);
v___x_2940_ = l_Lean_Syntax_matchesNull(v___x_2939_, v___x_2937_);
if (v___x_2940_ == 0)
{
lean_dec(v___x_2939_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_quotContext_x3f_2945_; lean_object* v___x_2946_; lean_object* v_a_2948_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v_quotContext_x3f_2945_ = lean_ctor_get(v_a_1747_, 5);
v___x_2946_ = l_Lean_SourceInfo_fromRef(v_a_2942_, v___x_2940_);
lean_dec(v_a_2942_);
if (lean_obj_tag(v_quotContext_x3f_2945_) == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v_a_2948_ = v_a_2980_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v___x_2946_);
lean_dec(v_a_2944_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2981_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_val_2989_; 
v_val_2989_ = lean_ctor_get(v_quotContext_x3f_2945_, 0);
lean_inc(v_val_2989_);
v_a_2948_ = v_val_2989_;
goto v___jp_2947_;
}
v___jp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2949_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2950_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2951_ = l_Lean_addMacroScope(v_a_2948_, v___x_2950_, v_a_2944_);
v___x_2952_ = lean_box(0);
lean_inc_n(v___x_2946_, 3);
v___x_2953_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2946_);
lean_ctor_set(v___x_2953_, 1, v___x_2949_);
lean_ctor_set(v___x_2953_, 2, v___x_2951_);
lean_ctor_set(v___x_2953_, 3, v___x_2952_);
v___x_2954_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2946_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_2957_ = l_Lean_Syntax_node1(v___x_2946_, v___x_2956_, v_stx_1746_);
v___x_2958_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2970_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2970_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2970_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2946_);
v___x_2964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2946_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = l_Lean_Syntax_node4(v___x_2946_, v___x_1758_, v___x_2953_, v___x_2955_, v___x_2957_, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_a_2959_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2966_);
v___x_2968_ = v___x_2961_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v___x_2957_);
lean_dec_ref(v___x_2955_);
lean_dec_ref(v___x_2953_);
lean_dec(v___x_2946_);
v_a_2971_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2958_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2958_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_a_2942_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2990_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2943_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2943_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_2998_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2941_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2941_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_val_3006_; lean_object* v___x_3007_; 
lean_dec(v_id_1745_);
v_val_3006_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3006_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3007_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3006_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
v_pat_1751_ = v_a_3008_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v_stx_1746_);
v_a_3009_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3007_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3017_ = l_Lean_Syntax_getArg(v___x_2939_, v___x_2704_);
lean_dec(v___x_2939_);
v___x_3018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3017_);
v___x_3019_ = l_Lean_Syntax_isOfKind(v___x_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_dec(v___x_3017_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_quotContext_x3f_3024_; lean_object* v___x_3025_; lean_object* v_a_3027_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref(v___x_3022_);
v_quotContext_x3f_3024_ = lean_ctor_get(v_a_1747_, 5);
v___x_3025_ = l_Lean_SourceInfo_fromRef(v_a_3021_, v___x_3019_);
lean_dec(v_a_3021_);
if (lean_obj_tag(v_quotContext_x3f_3024_) == 0)
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v_a_3027_ = v_a_3059_;
goto v___jp_3026_;
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3060_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3058_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v_val_3068_; 
v_val_3068_ = lean_ctor_get(v_quotContext_x3f_3024_, 0);
lean_inc(v_val_3068_);
v_a_3027_ = v_val_3068_;
goto v___jp_3026_;
}
v___jp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3028_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3029_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3030_ = l_Lean_addMacroScope(v_a_3027_, v___x_3029_, v_a_3023_);
v___x_3031_ = lean_box(0);
lean_inc_n(v___x_3025_, 3);
v___x_3032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3025_);
lean_ctor_set(v___x_3032_, 1, v___x_3028_);
lean_ctor_set(v___x_3032_, 2, v___x_3030_);
lean_ctor_set(v___x_3032_, 3, v___x_3031_);
v___x_3033_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3025_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3036_ = l_Lean_Syntax_node1(v___x_3025_, v___x_3035_, v_stx_1746_);
v___x_3037_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3049_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3049_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3049_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3025_);
v___x_3043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3025_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_Syntax_node4(v___x_3025_, v___x_1758_, v___x_3032_, v___x_3034_, v___x_3036_, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_a_3038_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3045_);
v___x_3047_ = v___x_3040_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v___x_3036_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v___x_3032_);
lean_dec(v___x_3025_);
v_a_3050_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3037_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3037_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_3021_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3069_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3022_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3022_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3077_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3020_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3020_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_val_3085_; lean_object* v___x_3086_; 
lean_dec(v_id_1745_);
v_val_3085_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3085_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3086_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3085_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
v_pat_1751_ = v_a_3087_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_stx_1746_);
v_a_3088_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3086_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3086_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3096_ = l_Lean_Syntax_getArg(v___x_3017_, v___x_2704_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3098_ = l_Lean_Syntax_matchesIdent(v___x_3096_, v___x_3097_);
lean_dec(v___x_3096_);
if (v___x_3098_ == 0)
{
lean_dec(v___x_3017_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref(v___x_3099_);
v___x_3101_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v_quotContext_x3f_3103_; lean_object* v___x_3104_; lean_object* v_a_3106_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3101_);
v_quotContext_x3f_3103_ = lean_ctor_get(v_a_1747_, 5);
v___x_3104_ = l_Lean_SourceInfo_fromRef(v_a_3100_, v___x_3098_);
lean_dec(v_a_3100_);
if (lean_obj_tag(v_quotContext_x3f_3103_) == 0)
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref(v___x_3137_);
v_a_3106_ = v_a_3138_;
goto v___jp_3105_;
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___x_3104_);
lean_dec(v_a_3102_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3139_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3137_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3137_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_val_3147_; 
v_val_3147_ = lean_ctor_get(v_quotContext_x3f_3103_, 0);
lean_inc(v_val_3147_);
v_a_3106_ = v_val_3147_;
goto v___jp_3105_;
}
v___jp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3107_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3108_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3109_ = l_Lean_addMacroScope(v_a_3106_, v___x_3108_, v_a_3102_);
v___x_3110_ = lean_box(0);
lean_inc_n(v___x_3104_, 3);
v___x_3111_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3104_);
lean_ctor_set(v___x_3111_, 1, v___x_3107_);
lean_ctor_set(v___x_3111_, 2, v___x_3109_);
lean_ctor_set(v___x_3111_, 3, v___x_3110_);
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3104_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3115_ = l_Lean_Syntax_node1(v___x_3104_, v___x_3114_, v_stx_1746_);
v___x_3116_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3128_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3128_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3128_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3121_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3104_);
v___x_3122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3104_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = l_Lean_Syntax_node4(v___x_3104_, v___x_1758_, v___x_3111_, v___x_3113_, v___x_3115_, v___x_3122_);
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v_a_3117_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3124_);
v___x_3126_ = v___x_3119_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v___x_3115_);
lean_dec_ref(v___x_3113_);
lean_dec_ref(v___x_3111_);
lean_dec(v___x_3104_);
v_a_3129_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3116_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3116_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_a_3100_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3148_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3101_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3101_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3156_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3099_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3099_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
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
else
{
lean_object* v_val_3164_; lean_object* v___x_3165_; 
lean_dec(v_id_1745_);
v_val_3164_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3164_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3165_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3164_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref(v___x_3165_);
v_pat_1751_ = v_a_3166_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_stx_1746_);
v_a_3167_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3165_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3165_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
else
{
lean_object* v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = l_Lean_Syntax_getArg(v___x_3017_, v___x_2937_);
lean_dec(v___x_3017_);
v___x_3176_ = l_Lean_Syntax_matchesNull(v___x_3175_, v___x_2704_);
if (v___x_3176_ == 0)
{
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
v___x_3179_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v_quotContext_x3f_3181_; lean_object* v___x_3182_; lean_object* v_a_3184_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v_quotContext_x3f_3181_ = lean_ctor_get(v_a_1747_, 5);
v___x_3182_ = l_Lean_SourceInfo_fromRef(v_a_3178_, v___x_3176_);
lean_dec(v_a_3178_);
if (lean_obj_tag(v_quotContext_x3f_3181_) == 0)
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref(v___x_3215_);
v_a_3184_ = v_a_3216_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v___x_3182_);
lean_dec(v_a_3180_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3217_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3215_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3215_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_val_3225_; 
v_val_3225_ = lean_ctor_get(v_quotContext_x3f_3181_, 0);
lean_inc(v_val_3225_);
v_a_3184_ = v_val_3225_;
goto v___jp_3183_;
}
v___jp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3185_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3186_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3187_ = l_Lean_addMacroScope(v_a_3184_, v___x_3186_, v_a_3180_);
v___x_3188_ = lean_box(0);
lean_inc_n(v___x_3182_, 3);
v___x_3189_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3182_);
lean_ctor_set(v___x_3189_, 1, v___x_3185_);
lean_ctor_set(v___x_3189_, 2, v___x_3187_);
lean_ctor_set(v___x_3189_, 3, v___x_3188_);
v___x_3190_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3182_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3193_ = l_Lean_Syntax_node1(v___x_3182_, v___x_3192_, v_stx_1746_);
v___x_3194_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3206_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3206_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3206_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3199_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3182_);
v___x_3200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3182_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_node4(v___x_3182_, v___x_1758_, v___x_3189_, v___x_3191_, v___x_3193_, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v_a_3195_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3202_);
v___x_3204_ = v___x_3197_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v___x_3193_);
lean_dec_ref(v___x_3191_);
lean_dec_ref(v___x_3189_);
lean_dec(v___x_3182_);
v_a_3207_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3194_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3194_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec(v_a_3178_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3226_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3179_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3179_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3234_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3177_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3177_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_val_3242_; lean_object* v___x_3243_; 
lean_dec(v_id_1745_);
v_val_3242_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3242_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3243_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3242_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref(v___x_3243_);
v_pat_1751_ = v_a_3244_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_stx_1746_);
v_a_3245_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3243_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3243_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
lean_dec(v_id_x3f_1744_);
v___x_3253_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3254_ = lean_box(0);
v___x_3255_ = l_Lean_Syntax_mkAntiquotNode(v___x_3253_, v_id_1745_, v___x_2704_, v___x_3254_, v___x_2711_);
v_pat_1751_ = v___x_3255_;
goto v___jp_1750_;
}
}
}
}
}
}
else
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
lean_dec(v___x_2705_);
v___x_3256_ = lean_unsigned_to_nat(1u);
v___x_3257_ = lean_unsigned_to_nat(2u);
v___x_3258_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_3257_);
lean_inc(v___x_3258_);
v___x_3259_ = l_Lean_Syntax_matchesNull(v___x_3258_, v___x_3256_);
if (v___x_3259_ == 0)
{
lean_dec(v___x_3258_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v_quotContext_x3f_3264_; lean_object* v___x_3265_; lean_object* v_a_3267_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref(v___x_3262_);
v_quotContext_x3f_3264_ = lean_ctor_get(v_a_1747_, 5);
v___x_3265_ = l_Lean_SourceInfo_fromRef(v_a_3261_, v___x_3259_);
lean_dec(v_a_3261_);
if (lean_obj_tag(v_quotContext_x3f_3264_) == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref(v___x_3298_);
v_a_3267_ = v_a_3299_;
goto v___jp_3266_;
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v___x_3265_);
lean_dec(v_a_3263_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3300_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3298_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_val_3308_; 
v_val_3308_ = lean_ctor_get(v_quotContext_x3f_3264_, 0);
lean_inc(v_val_3308_);
v_a_3267_ = v_val_3308_;
goto v___jp_3266_;
}
v___jp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3268_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3269_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3270_ = l_Lean_addMacroScope(v_a_3267_, v___x_3269_, v_a_3263_);
v___x_3271_ = lean_box(0);
lean_inc_n(v___x_3265_, 3);
v___x_3272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3265_);
lean_ctor_set(v___x_3272_, 1, v___x_3268_);
lean_ctor_set(v___x_3272_, 2, v___x_3270_);
lean_ctor_set(v___x_3272_, 3, v___x_3271_);
v___x_3273_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3265_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3276_ = l_Lean_Syntax_node1(v___x_3265_, v___x_3275_, v_stx_1746_);
v___x_3277_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3289_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3289_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3289_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3282_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3265_);
v___x_3283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3265_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_Syntax_node4(v___x_3265_, v___x_1758_, v___x_3272_, v___x_3274_, v___x_3276_, v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v_a_3278_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3285_);
v___x_3287_ = v___x_3280_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v___x_3276_);
lean_dec_ref(v___x_3274_);
lean_dec_ref(v___x_3272_);
lean_dec(v___x_3265_);
v_a_3290_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3277_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3277_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v_a_3261_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3309_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3262_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3262_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3317_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3260_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3260_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_val_3325_; lean_object* v___x_3326_; 
lean_dec(v_id_1745_);
v_val_3325_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3325_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3326_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3325_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v_pat_1751_ = v_a_3327_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_stx_1746_);
v_a_3328_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3326_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
else
{
lean_object* v_stx_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec(v_id_x3f_1744_);
v_stx_3336_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_2704_);
lean_dec(v___x_3258_);
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3338_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2708_, v_stx_3336_, v_id_1745_, v___x_3337_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref(v___x_3338_);
v_pat_1751_ = v_a_3339_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_stx_1746_);
v_a_3340_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3338_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3338_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
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
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
lean_dec(v___x_2705_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_unsigned_to_nat(2u);
v___x_3350_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_3349_);
lean_inc(v___x_3350_);
v___x_3351_ = l_Lean_Syntax_matchesNull(v___x_3350_, v___x_3348_);
if (v___x_3351_ == 0)
{
lean_dec(v___x_3350_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v_quotContext_x3f_3356_; lean_object* v___x_3357_; lean_object* v_a_3359_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref(v___x_3354_);
v_quotContext_x3f_3356_ = lean_ctor_get(v_a_1747_, 5);
v___x_3357_ = l_Lean_SourceInfo_fromRef(v_a_3353_, v___x_3351_);
lean_dec(v_a_3353_);
if (lean_obj_tag(v_quotContext_x3f_3356_) == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref(v___x_3390_);
v_a_3359_ = v_a_3391_;
goto v___jp_3358_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v___x_3357_);
lean_dec(v_a_3355_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3392_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3390_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3390_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v_val_3400_; 
v_val_3400_ = lean_ctor_get(v_quotContext_x3f_3356_, 0);
lean_inc(v_val_3400_);
v_a_3359_ = v_val_3400_;
goto v___jp_3358_;
}
v___jp_3358_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3360_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3362_ = l_Lean_addMacroScope(v_a_3359_, v___x_3361_, v_a_3355_);
v___x_3363_ = lean_box(0);
lean_inc_n(v___x_3357_, 3);
v___x_3364_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3357_);
lean_ctor_set(v___x_3364_, 1, v___x_3360_);
lean_ctor_set(v___x_3364_, 2, v___x_3362_);
lean_ctor_set(v___x_3364_, 3, v___x_3363_);
v___x_3365_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3357_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3368_ = l_Lean_Syntax_node1(v___x_3357_, v___x_3367_, v_stx_1746_);
v___x_3369_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3381_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3381_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3381_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3374_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3357_);
v___x_3375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3357_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = l_Lean_Syntax_node4(v___x_3357_, v___x_1758_, v___x_3364_, v___x_3366_, v___x_3368_, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v_a_3370_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3377_);
v___x_3379_ = v___x_3372_;
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
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v___x_3368_);
lean_dec_ref(v___x_3366_);
lean_dec_ref(v___x_3364_);
lean_dec(v___x_3357_);
v_a_3382_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3369_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3369_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v_a_3353_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3401_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3354_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3354_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3409_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3352_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3352_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3418_; 
lean_dec(v_id_1745_);
v_val_3417_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3417_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3418_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3417_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref(v___x_3418_);
v_pat_1751_ = v_a_3419_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec(v_stx_1746_);
v_a_3420_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3418_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
else
{
lean_object* v_stx_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec(v_id_x3f_1744_);
v_stx_3428_ = l_Lean_Syntax_getArg(v___x_3350_, v___x_2704_);
lean_dec(v___x_3350_);
v___x_3429_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3430_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2708_, v_stx_3428_, v_id_1745_, v___x_3429_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
v_pat_1751_ = v_a_3431_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v_stx_1746_);
v_a_3432_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3430_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3430_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
lean_dec(v___x_2705_);
v___x_3440_ = lean_unsigned_to_nat(1u);
v___x_3441_ = lean_unsigned_to_nat(2u);
v___x_3442_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_3441_);
lean_inc(v___x_3442_);
v___x_3443_ = l_Lean_Syntax_matchesNull(v___x_3442_, v___x_3440_);
if (v___x_3443_ == 0)
{
lean_dec(v___x_3442_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v_quotContext_x3f_3448_; lean_object* v___x_3449_; lean_object* v_a_3451_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v_quotContext_x3f_3448_ = lean_ctor_get(v_a_1747_, 5);
v___x_3449_ = l_Lean_SourceInfo_fromRef(v_a_3445_, v___x_3443_);
lean_dec(v_a_3445_);
if (lean_obj_tag(v_quotContext_x3f_3448_) == 0)
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref(v___x_3482_);
v_a_3451_ = v_a_3483_;
goto v___jp_3450_;
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec(v___x_3449_);
lean_dec(v_a_3447_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3484_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3482_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3482_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_val_3492_; 
v_val_3492_ = lean_ctor_get(v_quotContext_x3f_3448_, 0);
lean_inc(v_val_3492_);
v_a_3451_ = v_val_3492_;
goto v___jp_3450_;
}
v___jp_3450_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3452_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3453_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3454_ = l_Lean_addMacroScope(v_a_3451_, v___x_3453_, v_a_3447_);
v___x_3455_ = lean_box(0);
lean_inc_n(v___x_3449_, 3);
v___x_3456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3449_);
lean_ctor_set(v___x_3456_, 1, v___x_3452_);
lean_ctor_set(v___x_3456_, 2, v___x_3454_);
lean_ctor_set(v___x_3456_, 3, v___x_3455_);
v___x_3457_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3449_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3460_ = l_Lean_Syntax_node1(v___x_3449_, v___x_3459_, v_stx_1746_);
v___x_3461_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3473_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3473_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3473_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3466_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3449_);
v___x_3467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3449_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = l_Lean_Syntax_node4(v___x_3449_, v___x_1758_, v___x_3456_, v___x_3458_, v___x_3460_, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v_a_3462_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3469_);
v___x_3471_ = v___x_3464_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v___x_3460_);
lean_dec_ref(v___x_3458_);
lean_dec_ref(v___x_3456_);
lean_dec(v___x_3449_);
v_a_3474_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3461_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3461_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_a_3445_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3493_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3446_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3446_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3501_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3444_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3444_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v_val_3509_; lean_object* v___x_3510_; 
lean_dec(v_id_1745_);
v_val_3509_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3509_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3510_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3509_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref(v___x_3510_);
v_pat_1751_ = v_a_3511_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v_stx_1746_);
v_a_3512_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3510_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3510_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
else
{
lean_object* v_stx_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_dec(v_id_x3f_1744_);
v_stx_3520_ = l_Lean_Syntax_getArg(v___x_3442_, v___x_2704_);
lean_dec(v___x_3442_);
v___x_3521_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3522_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2706_, v_stx_3520_, v_id_1745_, v___x_3521_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref(v___x_3522_);
v_pat_1751_ = v_a_3523_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec(v_stx_1746_);
v_a_3524_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3522_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3522_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
}
v___jp_1759_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1765_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1767_ = l_Lean_addMacroScope(v_a_1764_, v___x_1766_, v___y_1761_);
v___x_1768_ = lean_box(0);
lean_inc_n(v___y_1762_, 3);
v___x_1769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1769_, 0, v___y_1762_);
lean_ctor_set(v___x_1769_, 1, v___x_1765_);
lean_ctor_set(v___x_1769_, 2, v___x_1767_);
lean_ctor_set(v___x_1769_, 3, v___x_1768_);
v___x_1770_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___y_1762_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_1773_ = l_Lean_Syntax_node1(v___y_1762_, v___x_1772_, v_stx_1746_);
v___x_1774_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v___y_1763_, v___y_1760_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1786_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1786_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1786_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1762_);
v___x_1780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___y_1762_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node4(v___y_1762_, v___x_1758_, v___x_1769_, v___x_1771_, v___x_1773_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_a_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1782_);
v___x_1784_ = v___x_1777_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v___x_1773_);
lean_dec_ref(v___x_1771_);
lean_dec_ref(v___x_1769_);
lean_dec(v___y_1762_);
v_a_1787_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1774_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1774_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
v___jp_1795_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1801_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1802_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1803_ = l_Lean_addMacroScope(v_a_1800_, v___x_1802_, v___y_1796_);
v___x_1804_ = lean_box(0);
lean_inc_n(v___y_1797_, 3);
v___x_1805_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1797_);
lean_ctor_set(v___x_1805_, 1, v___x_1801_);
lean_ctor_set(v___x_1805_, 2, v___x_1803_);
lean_ctor_set(v___x_1805_, 3, v___x_1804_);
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___y_1797_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_1809_ = l_Lean_Syntax_node1(v___y_1797_, v___x_1808_, v_stx_1746_);
v___x_1810_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1822_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1797_);
v___x_1816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1797_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_Syntax_node4(v___y_1797_, v___x_1758_, v___x_1805_, v___x_1807_, v___x_1809_, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_a_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1818_);
v___x_1820_ = v___x_1813_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v___x_1809_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1805_);
lean_dec(v___y_1797_);
v_a_1823_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1810_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1810_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3532_ = lean_unsigned_to_nat(1u);
v___x_3533_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_3532_);
v___x_3534_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3533_);
v___x_3535_ = l_Lean_Syntax_isOfKind(v___x_3533_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_dec(v___x_3533_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v_quotContext_x3f_3540_; lean_object* v___x_3541_; lean_object* v_a_3543_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref(v___x_3538_);
v_quotContext_x3f_3540_ = lean_ctor_get(v_a_1747_, 5);
v___x_3541_ = l_Lean_SourceInfo_fromRef(v_a_3537_, v___x_3535_);
lean_dec(v_a_3537_);
if (lean_obj_tag(v_quotContext_x3f_3540_) == 0)
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref(v___x_3575_);
v_a_3543_ = v_a_3576_;
goto v___jp_3542_;
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v___x_3541_);
lean_dec(v_a_3539_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3577_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3575_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3575_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v_val_3585_; 
v_val_3585_ = lean_ctor_get(v_quotContext_x3f_3540_, 0);
lean_inc(v_val_3585_);
v_a_3543_ = v_val_3585_;
goto v___jp_3542_;
}
v___jp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3544_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3545_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3546_ = l_Lean_addMacroScope(v_a_3543_, v___x_3545_, v_a_3539_);
v___x_3547_ = lean_box(0);
lean_inc_n(v___x_3541_, 3);
v___x_3548_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3541_);
lean_ctor_set(v___x_3548_, 1, v___x_3544_);
lean_ctor_set(v___x_3548_, 2, v___x_3546_);
lean_ctor_set(v___x_3548_, 3, v___x_3547_);
v___x_3549_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3541_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3552_ = l_Lean_Syntax_node1(v___x_3541_, v___x_3551_, v_stx_1746_);
v___x_3553_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3566_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3566_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3566_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3541_);
v___x_3559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3541_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3561_ = l_Lean_Syntax_node4(v___x_3541_, v___x_3560_, v___x_3548_, v___x_3550_, v___x_3552_, v___x_3559_);
v___x_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v_a_3554_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3562_);
v___x_3564_ = v___x_3556_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v___x_3552_);
lean_dec_ref(v___x_3550_);
lean_dec_ref(v___x_3548_);
lean_dec(v___x_3541_);
v_a_3567_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3553_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3553_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_a_3537_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3586_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3538_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3538_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3594_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3536_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3536_);
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
else
{
lean_object* v_val_3602_; lean_object* v___x_3603_; 
lean_dec(v_id_1745_);
v_val_3602_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3602_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3603_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3602_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
v_pat_1751_ = v_a_3604_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v_stx_1746_);
v_a_3605_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3603_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3603_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_dec(v_id_x3f_1744_);
v___x_3613_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3613_, 0, v___x_3533_);
v___x_3614_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3613_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v___x_3616_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3617_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3618_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3619_ = lean_unsigned_to_nat(4u);
v___x_3620_ = lean_mk_empty_array_with_capacity(v___x_3619_);
v___x_3621_ = lean_array_push(v___x_3620_, v_a_3615_);
v___x_3622_ = lean_array_push(v___x_3621_, v___x_3617_);
v___x_3623_ = lean_array_push(v___x_3622_, v___x_3618_);
v___x_3624_ = lean_array_push(v___x_3623_, v_id_1745_);
v___x_3625_ = lean_box(2);
v___x_3626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set(v___x_3626_, 1, v___x_3616_);
lean_ctor_set(v___x_3626_, 2, v___x_3624_);
v_pat_1751_ = v___x_3626_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3627_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3614_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3614_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = l_Lean_Syntax_getArg(v_stx_1746_, v___x_3635_);
v___x_3637_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3636_);
v___x_3638_ = l_Lean_Syntax_isOfKind(v___x_3636_, v___x_3637_);
if (v___x_3638_ == 0)
{
lean_dec(v___x_3636_);
if (lean_obj_tag(v_id_x3f_1744_) == 0)
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_Elab_Command_getRef___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3641_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref(v___x_3639_);
v___x_3641_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1747_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v_quotContext_x3f_3643_; lean_object* v___x_3644_; lean_object* v_a_3646_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref(v___x_3641_);
v_quotContext_x3f_3643_ = lean_ctor_get(v_a_1747_, 5);
v___x_3644_ = l_Lean_SourceInfo_fromRef(v_a_3640_, v___x_3638_);
lean_dec(v_a_3640_);
if (lean_obj_tag(v_quotContext_x3f_3643_) == 0)
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1748_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
v_a_3646_ = v_a_3679_;
goto v___jp_3645_;
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec(v___x_3644_);
lean_dec(v_a_3642_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3680_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3678_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3678_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_val_3688_; 
v_val_3688_ = lean_ctor_get(v_quotContext_x3f_3643_, 0);
lean_inc(v_val_3688_);
v_a_3646_ = v_val_3688_;
goto v___jp_3645_;
}
v___jp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3647_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3648_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3649_ = l_Lean_addMacroScope(v_a_3646_, v___x_3648_, v_a_3642_);
v___x_3650_ = lean_box(0);
lean_inc_n(v___x_3644_, 3);
v___x_3651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3644_);
lean_ctor_set(v___x_3651_, 1, v___x_3647_);
lean_ctor_set(v___x_3651_, 2, v___x_3649_);
lean_ctor_set(v___x_3651_, 3, v___x_3650_);
v___x_3652_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3644_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1746_);
v___x_3655_ = l_Lean_Syntax_node1(v___x_3644_, v___x_3654_, v_stx_1746_);
v___x_3656_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_id_1745_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3669_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3669_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3669_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3644_);
v___x_3662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3644_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3664_ = l_Lean_Syntax_node4(v___x_3644_, v___x_3663_, v___x_3651_, v___x_3653_, v___x_3655_, v___x_3662_);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
lean_ctor_set(v___x_3665_, 1, v_a_3657_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v___x_3665_);
v___x_3667_ = v___x_3659_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___x_3655_);
lean_dec_ref(v___x_3653_);
lean_dec_ref(v___x_3651_);
lean_dec(v___x_3644_);
v_a_3670_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3656_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3656_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_a_3640_);
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3689_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3641_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3641_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3697_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3639_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3639_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
else
{
lean_object* v_val_3705_; lean_object* v___x_3706_; 
lean_dec(v_id_1745_);
v_val_3705_ = lean_ctor_get(v_id_x3f_1744_, 0);
lean_inc(v_val_3705_);
lean_dec_ref(v_id_x3f_1744_);
lean_inc(v_stx_1746_);
v___x_3706_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1746_, v_val_3705_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref(v___x_3706_);
v_pat_1751_ = v_a_3707_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v_stx_1746_);
v_a_3708_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3706_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3706_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec(v_id_x3f_1744_);
v___x_3716_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3716_, 0, v___x_3636_);
v___x_3717_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3716_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3720_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3721_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3722_ = lean_unsigned_to_nat(4u);
v___x_3723_ = lean_mk_empty_array_with_capacity(v___x_3722_);
v___x_3724_ = lean_array_push(v___x_3723_, v_a_3718_);
v___x_3725_ = lean_array_push(v___x_3724_, v___x_3720_);
v___x_3726_ = lean_array_push(v___x_3725_, v___x_3721_);
v___x_3727_ = lean_array_push(v___x_3726_, v_id_1745_);
v___x_3728_ = lean_box(2);
v___x_3729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
lean_ctor_set(v___x_3729_, 1, v___x_3719_);
lean_ctor_set(v___x_3729_, 2, v___x_3727_);
v_pat_1751_ = v___x_3729_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_stx_1746_);
lean_dec(v_id_1745_);
v_a_3730_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3717_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3717_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
v___jp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_stx_1746_);
lean_ctor_set(v___x_1752_, 1, v_pat_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3738_, lean_object* v_id_3739_, lean_object* v_stx_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3738_, v_id_3739_, v_stx_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3746_, v___y_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3750_, lean_object* v_x_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3750_, v_x_3751_, v___y_3752_, v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec_ref(v_x_3751_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3755_, lean_object* v_ref_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3756_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3761_, lean_object* v_ref_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3761_, v_ref_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3777_, lean_object* v_x_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3783_, lean_object* v_x_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3783_, v_x_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3789_, lean_object* v_as_x27_3790_, lean_object* v_b_3791_, lean_object* v_a_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3790_, v_b_3791_, v___y_3793_, v___y_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3797_, lean_object* v_as_x27_3798_, lean_object* v_b_3799_, lean_object* v_a_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3797_, v_as_x27_3798_, v_b_3799_, v_a_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v_as_3797_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3805_, lean_object* v_ref_3806_, lean_object* v_msg_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3806_, v_msg_3807_, v___y_3808_, v___y_3809_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3812_, lean_object* v_ref_3813_, lean_object* v_msg_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3812_, v_ref_3813_, v_msg_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v_ref_3813_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3819_, lean_object* v_m_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3820_, v_a_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3823_, lean_object* v_m_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3823_, v_m_3824_, v_a_3825_);
lean_dec(v_a_3825_);
lean_dec_ref(v_m_3824_);
return v_res_3826_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3827_, lean_object* v_x_3828_, lean_object* v_x_3829_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3828_, v_x_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3831_, lean_object* v_x_3832_, lean_object* v_x_3833_){
_start:
{
uint8_t v_res_3834_; lean_object* v_r_3835_; 
v_res_3834_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_3831_, v_x_3832_, v_x_3833_);
lean_dec_ref(v_x_3833_);
lean_dec_ref(v_x_3832_);
v_r_3835_ = lean_box(v_res_3834_);
return v_r_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3836_, lean_object* v_a_3837_, lean_object* v_x_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_3837_, v_x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3840_, lean_object* v_a_3841_, lean_object* v_x_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_3840_, v_a_3841_, v_x_3842_);
lean_dec(v_x_3842_);
lean_dec(v_a_3841_);
return v_res_3843_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3844_, lean_object* v_x_3845_, size_t v_x_3846_, lean_object* v_x_3847_){
_start:
{
uint8_t v___x_3848_; 
v___x_3848_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_3845_, v_x_3846_, v_x_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3849_, lean_object* v_x_3850_, lean_object* v_x_3851_, lean_object* v_x_3852_){
_start:
{
size_t v_x_90430__boxed_3853_; uint8_t v_res_3854_; lean_object* v_r_3855_; 
v_x_90430__boxed_3853_ = lean_unbox_usize(v_x_3851_);
lean_dec(v_x_3851_);
v_res_3854_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_3849_, v_x_3850_, v_x_90430__boxed_3853_, v_x_3852_);
lean_dec_ref(v_x_3852_);
lean_dec_ref(v_x_3850_);
v_r_3855_ = lean_box(v_res_3854_);
return v_r_3855_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_3856_, lean_object* v_keys_3857_, lean_object* v_vals_3858_, lean_object* v_heq_3859_, lean_object* v_i_3860_, lean_object* v_k_3861_){
_start:
{
uint8_t v___x_3862_; 
v___x_3862_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_3857_, v_i_3860_, v_k_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3863_, lean_object* v_keys_3864_, lean_object* v_vals_3865_, lean_object* v_heq_3866_, lean_object* v_i_3867_, lean_object* v_k_3868_){
_start:
{
uint8_t v_res_3869_; lean_object* v_r_3870_; 
v_res_3869_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_3863_, v_keys_3864_, v_vals_3865_, v_heq_3866_, v_i_3867_, v_k_3868_);
lean_dec_ref(v_k_3868_);
lean_dec_ref(v_vals_3865_);
lean_dec_ref(v_keys_3864_);
v_r_3870_ = lean_box(v_res_3869_);
return v_r_3870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_k_3877_){
_start:
{
lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_3879_ = lean_name_eq(v_k_3877_, v___x_3878_);
if (v___x_3879_ == 0)
{
uint8_t v___x_3880_; 
v___x_3880_ = 1;
return v___x_3880_;
}
else
{
uint8_t v___x_3881_; 
v___x_3881_ = 0;
return v___x_3881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_k_3882_){
_start:
{
uint8_t v_res_3883_; lean_object* v_r_3884_; 
v_res_3883_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_3882_);
lean_dec(v_k_3882_);
v_r_3884_ = lean_box(v_res_3883_);
return v_r_3884_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_3895_ = l_String_toRawSubstring_x27(v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v___f_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___f_3902_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_3903_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_3903_, 0, v_stx_3898_);
lean_closure_set(v___x_3903_, 1, v___f_3902_);
v___x_3904_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3903_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc_n(v_a_3905_, 2);
lean_dec_ref(v___x_3904_);
v___x_3906_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_3907_ = l_Lean_Syntax_isOfKind(v_a_3905_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec(v_a_3905_);
v___x_3908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = l_Lean_Syntax_getArg(v_a_3905_, v___x_3917_);
v___x_3919_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3918_);
v___x_3920_ = l_Lean_Syntax_matchesNull(v___x_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_Syntax_matchesNull(v___x_3918_, v___x_3917_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_a_3905_);
v___x_3922_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3922_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
else
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Elab_Command_getRef___redArg(v_a_3899_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref(v___x_3931_);
v___x_3933_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3899_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v_quotContext_x3f_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v_a_3940_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v_quotContext_x3f_3935_ = lean_ctor_get(v_a_3899_, 5);
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = l_Lean_Syntax_getArg(v_a_3905_, v___x_3936_);
lean_dec(v_a_3905_);
v___x_3938_ = l_Lean_SourceInfo_fromRef(v_a_3932_, v___x_3920_);
lean_dec(v_a_3932_);
if (lean_obj_tag(v_quotContext_x3f_3935_) == 0)
{
lean_object* v___x_3948_; lean_object* v_a_3949_; 
v___x_3948_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_3900_);
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_a_3949_);
lean_dec_ref(v___x_3948_);
v_a_3940_ = v_a_3949_;
goto v___jp_3939_;
}
else
{
lean_object* v_val_3950_; 
v_val_3950_ = lean_ctor_get(v_quotContext_x3f_3935_, 0);
lean_inc(v_val_3950_);
v_a_3940_ = v_val_3950_;
goto v___jp_3939_;
}
v___jp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3941_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_3943_ = l_Lean_addMacroScope(v_a_3940_, v___x_3942_, v_a_3934_);
v___x_3944_ = lean_box(0);
v___x_3945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3938_);
lean_ctor_set(v___x_3945_, 1, v___x_3941_);
lean_ctor_set(v___x_3945_, 2, v___x_3943_);
lean_ctor_set(v___x_3945_, 3, v___x_3944_);
v___x_3946_ = lean_box(0);
v___x_3947_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3946_, v___x_3945_, v___x_3937_, v_a_3899_, v_a_3900_);
return v___x_3947_;
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v_a_3932_);
lean_dec(v_a_3905_);
v_a_3951_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3933_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3933_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v_a_3905_);
v_a_3959_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3931_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3931_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3967_ = l_Lean_Syntax_getArg(v___x_3918_, v___x_3917_);
lean_dec(v___x_3918_);
v___x_3968_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_3967_);
v___x_3969_ = l_Lean_Syntax_isOfKind(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v___x_3967_);
lean_dec(v_a_3905_);
v___x_3970_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = l_Lean_Syntax_getArg(v_a_3905_, v___x_3979_);
lean_dec(v_a_3905_);
lean_inc(v___x_3967_);
v___x_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3967_);
v___x_3982_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3981_, v___x_3967_, v___x_3980_, v_a_3899_, v_a_3900_);
return v___x_3982_;
}
}
}
}
else
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
v_a_3983_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3904_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3904_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_Elab_Command_expandMacroArg(v_stx_3991_, v_a_3992_, v_a_3993_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
return v_res_3995_;
}
}
lean_object* runtime_initialize_Lean_Elab_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_MacroArgUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_MacroArgUtil(builtin);
}
#ifdef __cplusplus
}
#endif
