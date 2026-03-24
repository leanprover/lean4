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
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
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
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
lean_ctor_set(v___x_359_, 3, v___x_357_);
lean_ctor_set(v___x_359_, 4, v___x_357_);
lean_ctor_set(v___x_359_, 5, v___x_357_);
lean_ctor_set(v___x_359_, 6, v___x_357_);
lean_ctor_set(v___x_359_, 7, v___x_357_);
lean_ctor_set(v___x_359_, 8, v___x_357_);
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
lean_inc(v_macroStack_398_);
lean_dec_ref(v___y_393_);
v___x_399_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_392_, v___y_394_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_399_);
lean_inc(v_macroStack_398_);
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
lean_dec_ref(v___y_393_);
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
uint8_t v___x_28754__boxed_511_; size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v___x_28754__boxed_511_ = lean_unbox(v___x_503_);
v_i_boxed_512_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_28754__boxed_511_, v_as_504_, v_i_boxed_512_, v_stop_boxed_513_, v_b_507_, v___y_508_, v___y_509_);
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
lean_inc_ref(v___y_650_);
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
lean_inc_ref(v___y_816_);
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
v___x_893_ = lean_panic_fn(v___x_892_, v_msg_891_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_box(0);
v___x_895_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg(){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___closed__0);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg___boxed(lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
return v_res_901_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = l_Lean_maxRecDepthErrorMessage;
v___x_908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__3);
v___x_910_ = l_Lean_MessageData_ofFormat(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__4);
v___x_912_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__2));
v___x_913_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(lean_object* v_ref_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__5);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_ref_914_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v_ref_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(v_ref_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_922_, lean_object* v_declName_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v___x_926_; lean_object* v_env_927_; lean_object* v___x_928_; uint8_t v___x_929_; uint8_t v___x_930_; 
v___x_926_ = 0;
v_env_927_ = l_Lean_Environment_setExporting(v_env_922_, v___x_926_);
lean_inc(v_declName_923_);
v___x_928_ = l_Lean_mkPrivateName(v_env_927_, v_declName_923_);
v___x_929_ = 1;
lean_inc_ref(v_env_927_);
v___x_930_ = l_Lean_Environment_contains(v_env_927_, v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_931_ = l_Lean_privateToUserName(v_declName_923_);
v___x_932_ = l_Lean_Environment_contains(v_env_927_, v___x_931_, v___x_929_);
v___x_933_ = lean_box(v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___y_925_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v_env_927_);
lean_dec(v_declName_923_);
v___x_935_ = lean_box(v___x_930_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___y_925_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_937_, lean_object* v_declName_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_937_, v_declName_938_, v___y_939_, v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_942_, lean_object* v_opts_943_, lean_object* v_currNamespace_944_, lean_object* v_openDecls_945_, lean_object* v_n_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l_Lean_ResolveName_resolveGlobalName(v_env_942_, v_opts_943_, v_currNamespace_944_, v_openDecls_945_, v_n_946_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___y_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_951_, lean_object* v_opts_952_, lean_object* v_currNamespace_953_, lean_object* v_openDecls_954_, lean_object* v_n_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_951_, v_opts_952_, v_currNamespace_953_, v_openDecls_954_, v_n_955_, v___y_956_, v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v_opts_952_);
return v_res_958_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_959_; double v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_float_of_nat(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_cls_963_, lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Elab_Command_getRef___redArg(v___y_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1017_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_964_, v___y_966_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1017_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1017_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v_traceState_976_; lean_object* v_env_977_; lean_object* v_messages_978_; lean_object* v_scopes_979_; lean_object* v_usedQuotCtxts_980_; lean_object* v_nextMacroScope_981_; lean_object* v_maxRecDepth_982_; lean_object* v_ngen_983_; lean_object* v_auxDeclNGen_984_; lean_object* v_infoState_985_; lean_object* v_snapshotTasks_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1016_; 
v___x_975_ = lean_st_ref_take(v___y_966_);
v_traceState_976_ = lean_ctor_get(v___x_975_, 9);
v_env_977_ = lean_ctor_get(v___x_975_, 0);
v_messages_978_ = lean_ctor_get(v___x_975_, 1);
v_scopes_979_ = lean_ctor_get(v___x_975_, 2);
v_usedQuotCtxts_980_ = lean_ctor_get(v___x_975_, 3);
v_nextMacroScope_981_ = lean_ctor_get(v___x_975_, 4);
v_maxRecDepth_982_ = lean_ctor_get(v___x_975_, 5);
v_ngen_983_ = lean_ctor_get(v___x_975_, 6);
v_auxDeclNGen_984_ = lean_ctor_get(v___x_975_, 7);
v_infoState_985_ = lean_ctor_get(v___x_975_, 8);
v_snapshotTasks_986_ = lean_ctor_get(v___x_975_, 10);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_988_ = v___x_975_;
v_isShared_989_ = v_isSharedCheck_1016_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snapshotTasks_986_);
lean_inc(v_traceState_976_);
lean_inc(v_infoState_985_);
lean_inc(v_auxDeclNGen_984_);
lean_inc(v_ngen_983_);
lean_inc(v_maxRecDepth_982_);
lean_inc(v_nextMacroScope_981_);
lean_inc(v_usedQuotCtxts_980_);
lean_inc(v_scopes_979_);
lean_inc(v_messages_978_);
lean_inc(v_env_977_);
lean_dec(v___x_975_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1016_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint64_t v_tid_990_; lean_object* v_traces_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1015_; 
v_tid_990_ = lean_ctor_get_uint64(v_traceState_976_, sizeof(void*)*1);
v_traces_991_ = lean_ctor_get(v_traceState_976_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_traceState_976_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_993_ = v_traceState_976_;
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_traces_991_);
lean_dec(v_traceState_976_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; double v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_995_ = lean_box(0);
v___x_996_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__0);
v___x_997_ = 0;
v___x_998_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_999_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_999_, 0, v_cls_963_);
lean_ctor_set(v___x_999_, 1, v___x_995_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
lean_ctor_set_float(v___x_999_, sizeof(void*)*3, v___x_996_);
lean_ctor_set_float(v___x_999_, sizeof(void*)*3 + 8, v___x_996_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*3 + 16, v___x_997_);
v___x_1000_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___closed__1));
v___x_1001_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v_a_971_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_969_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_PersistentArray_push___redArg(v_traces_991_, v___x_1002_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1003_);
v___x_1005_ = v___x_993_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1003_);
lean_ctor_set_uint64(v_reuseFailAlloc_1014_, sizeof(void*)*1, v_tid_990_);
v___x_1005_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 9, v___x_1005_);
v___x_1007_ = v___x_988_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_env_977_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_messages_978_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_scopes_979_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_usedQuotCtxts_980_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_nextMacroScope_981_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v_maxRecDepth_982_);
lean_ctor_set(v_reuseFailAlloc_1013_, 6, v_ngen_983_);
lean_ctor_set(v_reuseFailAlloc_1013_, 7, v_auxDeclNGen_984_);
lean_ctor_set(v_reuseFailAlloc_1013_, 8, v_infoState_985_);
lean_ctor_set(v_reuseFailAlloc_1013_, 9, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 10, v_snapshotTasks_986_);
v___x_1007_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = lean_st_ref_set(v___y_966_, v___x_1007_);
v___x_1009_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1009_);
v___x_1011_ = v___x_973_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_msg_964_);
lean_dec(v_cls_963_);
v_a_1018_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_968_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_968_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_cls_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_cls_1026_, v_msg_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg(lean_object* v_cls_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_scopes_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_opts_1044_; uint8_t v_hasTrace_1045_; 
v___x_1038_ = l_Lean_inheritedTraceOptions;
v___x_1039_ = lean_st_ref_get(v___x_1038_);
v___x_1040_ = lean_st_ref_get(v___y_1036_);
v_scopes_1041_ = lean_ctor_get(v___x_1040_, 2);
lean_inc(v_scopes_1041_);
lean_dec(v___x_1040_);
v___x_1042_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1043_ = l_List_head_x21___redArg(v___x_1042_, v_scopes_1041_);
lean_dec(v_scopes_1041_);
v_opts_1044_ = lean_ctor_get(v___x_1043_, 1);
lean_inc_ref(v_opts_1044_);
lean_dec(v___x_1043_);
v_hasTrace_1045_ = lean_ctor_get_uint8(v_opts_1044_, sizeof(void*)*1);
if (v_hasTrace_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v_opts_1044_);
lean_dec(v___x_1039_);
lean_dec(v_cls_1035_);
v___x_1046_ = lean_box(v_hasTrace_1045_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___closed__1));
v___x_1049_ = l_Lean_Name_append(v___x_1048_, v_cls_1035_);
v___x_1050_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1039_, v_opts_1044_, v___x_1049_);
lean_dec(v___x_1049_);
lean_dec_ref(v_opts_1044_);
lean_dec(v___x_1039_);
v___x_1051_ = lean_box(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg___boxed(lean_object* v_cls_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg(v_cls_1053_, v___y_1054_);
lean_dec(v___y_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1057_, lean_object* v_i_1058_, lean_object* v_k_1059_){
_start:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_get_size(v_keys_1057_);
v___x_1061_ = lean_nat_dec_lt(v_i_1058_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v_i_1058_);
return v___x_1061_;
}
else
{
lean_object* v_k_x27_1062_; uint8_t v___x_1063_; 
v_k_x27_1062_ = lean_array_fget_borrowed(v_keys_1057_, v_i_1058_);
v___x_1063_ = l_Lean_instBEqExtraModUse_beq(v_k_1059_, v_k_x27_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_i_1058_, v___x_1064_);
lean_dec(v_i_1058_);
v_i_1058_ = v___x_1065_;
goto _start;
}
else
{
lean_dec(v_i_1058_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1067_, lean_object* v_i_1068_, lean_object* v_k_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_1067_, v_i_1068_, v_k_1069_);
lean_dec_ref(v_k_1069_);
lean_dec_ref(v_keys_1067_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__0(void){
_start:
{
size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; 
v___x_1072_ = ((size_t)5ULL);
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_shift_left(v___x_1073_, v___x_1072_);
return v___x_1074_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__1(void){
_start:
{
size_t v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; 
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__0);
v___x_1077_ = lean_usize_sub(v___x_1076_, v___x_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg(lean_object* v_x_1078_, size_t v_x_1079_, lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_object* v_es_1081_; lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; lean_object* v_j_1086_; lean_object* v___x_1087_; 
v_es_1081_ = lean_ctor_get(v_x_1078_, 0);
lean_inc_ref(v_es_1081_);
lean_dec_ref(v_x_1078_);
v___x_1082_ = lean_box(2);
v___x_1083_ = ((size_t)5ULL);
v___x_1084_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___closed__1);
v___x_1085_ = lean_usize_land(v_x_1079_, v___x_1084_);
v_j_1086_ = lean_usize_to_nat(v___x_1085_);
v___x_1087_ = lean_array_get(v___x_1082_, v_es_1081_, v_j_1086_);
lean_dec(v_j_1086_);
lean_dec_ref(v_es_1081_);
switch(lean_obj_tag(v___x_1087_))
{
case 0:
{
lean_object* v_key_1088_; uint8_t v___x_1089_; 
v_key_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_key_1088_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = l_Lean_instBEqExtraModUse_beq(v_x_1080_, v_key_1088_);
lean_dec(v_key_1088_);
return v___x_1089_;
}
case 1:
{
lean_object* v_node_1090_; size_t v___x_1091_; 
v_node_1090_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_node_1090_);
lean_dec_ref(v___x_1087_);
v___x_1091_ = lean_usize_shift_right(v_x_1079_, v___x_1083_);
v_x_1078_ = v_node_1090_;
v_x_1079_ = v___x_1091_;
goto _start;
}
default: 
{
uint8_t v___x_1093_; 
v___x_1093_ = 0;
return v___x_1093_;
}
}
}
else
{
lean_object* v_ks_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_ks_1094_ = lean_ctor_get(v_x_1078_, 0);
lean_inc_ref(v_ks_1094_);
lean_dec_ref(v_x_1078_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_ks_1094_, v___x_1095_, v_x_1080_);
lean_dec_ref(v_ks_1094_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
size_t v_x_84555__boxed_1100_; uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_x_84555__boxed_1100_ = lean_unbox_usize(v_x_1098_);
lean_dec(v_x_1098_);
v_res_1101_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1097_, v_x_84555__boxed_1100_, v_x_1099_);
lean_dec_ref(v_x_1099_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint64_t v___x_1105_; size_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = l_Lean_instHashableExtraModUse_hash(v_x_1104_);
v___x_1106_ = lean_uint64_to_usize(v___x_1105_);
v___x_1107_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1103_, v___x_1106_, v_x_1104_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg(v_x_1108_, v_x_1109_);
lean_dec_ref(v_x_1109_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__1));
v___x_1115_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__0));
v___x_1116_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__5));
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__7));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__9));
v___x_1128_ = l_Lean_stringToMessageData(v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__11));
v___x_1131_ = l_Lean_stringToMessageData(v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6(lean_object* v_mod_1136_, uint8_t v_isMeta_1137_, lean_object* v_hint_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v_env_1143_; uint8_t v_isExporting_1144_; lean_object* v___x_1145_; lean_object* v_env_1146_; lean_object* v___x_1147_; lean_object* v_entry_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___y_1153_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1142_ = lean_st_ref_get(v___y_1140_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_env_1143_);
lean_dec(v___x_1142_);
v_isExporting_1144_ = lean_ctor_get_uint8(v_env_1143_, sizeof(void*)*8);
lean_dec_ref(v_env_1143_);
v___x_1145_ = lean_st_ref_get(v___y_1140_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref(v_env_1146_);
lean_dec(v___x_1145_);
v___x_1147_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__2);
lean_inc(v_mod_1136_);
v_entry_1148_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1148_, 0, v_mod_1136_);
lean_ctor_set_uint8(v_entry_1148_, sizeof(void*)*1, v_isExporting_1144_);
lean_ctor_set_uint8(v_entry_1148_, sizeof(void*)*1 + 1, v_isMeta_1137_);
v___x_1149_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1150_ = lean_box(1);
v___x_1151_ = lean_box(0);
v___x_1179_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1147_, v___x_1149_, v_env_1146_, v___x_1150_, v___x_1151_);
v___x_1180_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg(v___x_1179_, v_entry_1148_);
if (v___x_1180_ == 0)
{
lean_object* v_cls_1181_; lean_object* v___x_1182_; lean_object* v_a_1183_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___x_1204_; 
v_cls_1181_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__4));
v___x_1182_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg(v_cls_1181_, v___y_1140_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___x_1204_ = lean_unbox(v_a_1183_);
lean_dec(v_a_1183_);
if (v___x_1204_ == 0)
{
lean_dec(v_hint_1138_);
lean_dec(v_mod_1136_);
v___y_1153_ = v___y_1140_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1205_; lean_object* v___y_1207_; 
v___x_1205_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__10);
if (v_isExporting_1144_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__15));
v___y_1207_ = v___x_1214_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1215_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__16));
v___y_1207_ = v___x_1215_;
goto v___jp_1206_;
}
v___jp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1208_ = l_Lean_stringToMessageData(v___y_1207_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1205_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__12);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
if (v_isMeta_1137_ == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__13));
v___y_1190_ = v___x_1211_;
v___y_1191_ = v___x_1212_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1213_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__14));
v___y_1190_ = v___x_1211_;
v___y_1191_ = v___x_1213_;
goto v___jp_1189_;
}
}
}
v___jp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___y_1185_);
lean_ctor_set(v___x_1187_, 1, v___y_1186_);
v___x_1188_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_cls_1181_, v___x_1187_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_dec_ref(v___x_1188_);
v___y_1153_ = v___y_1140_;
goto v___jp_1152_;
}
else
{
lean_dec_ref(v_entry_1148_);
return v___x_1188_;
}
}
v___jp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1192_ = l_Lean_stringToMessageData(v___y_1191_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1190_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__6);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_MessageData_ofName(v_mod_1136_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = l_Lean_Name_isAnonymous(v_hint_1138_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___closed__8);
v___x_1200_ = l_Lean_MessageData_ofName(v_hint_1138_);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___y_1185_ = v___x_1197_;
v___y_1186_ = v___x_1201_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec(v_hint_1138_);
v___x_1202_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1203_ = l_Lean_stringToMessageData(v___x_1202_);
v___y_1185_ = v___x_1197_;
v___y_1186_ = v___x_1203_;
goto v___jp_1184_;
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_entry_1148_);
lean_dec(v_hint_1138_);
lean_dec(v_mod_1136_);
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v_toEnvExtension_1155_; lean_object* v_env_1156_; lean_object* v_messages_1157_; lean_object* v_scopes_1158_; lean_object* v_usedQuotCtxts_1159_; lean_object* v_nextMacroScope_1160_; lean_object* v_maxRecDepth_1161_; lean_object* v_ngen_1162_; lean_object* v_auxDeclNGen_1163_; lean_object* v_infoState_1164_; lean_object* v_traceState_1165_; lean_object* v_snapshotTasks_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1178_; 
v___x_1154_ = lean_st_ref_take(v___y_1153_);
v_toEnvExtension_1155_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_toEnvExtension_1155_);
v_env_1156_ = lean_ctor_get(v___x_1154_, 0);
v_messages_1157_ = lean_ctor_get(v___x_1154_, 1);
v_scopes_1158_ = lean_ctor_get(v___x_1154_, 2);
v_usedQuotCtxts_1159_ = lean_ctor_get(v___x_1154_, 3);
v_nextMacroScope_1160_ = lean_ctor_get(v___x_1154_, 4);
v_maxRecDepth_1161_ = lean_ctor_get(v___x_1154_, 5);
v_ngen_1162_ = lean_ctor_get(v___x_1154_, 6);
v_auxDeclNGen_1163_ = lean_ctor_get(v___x_1154_, 7);
v_infoState_1164_ = lean_ctor_get(v___x_1154_, 8);
v_traceState_1165_ = lean_ctor_get(v___x_1154_, 9);
v_snapshotTasks_1166_ = lean_ctor_get(v___x_1154_, 10);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1168_ = v___x_1154_;
v_isShared_1169_ = v_isSharedCheck_1178_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snapshotTasks_1166_);
lean_inc(v_traceState_1165_);
lean_inc(v_infoState_1164_);
lean_inc(v_auxDeclNGen_1163_);
lean_inc(v_ngen_1162_);
lean_inc(v_maxRecDepth_1161_);
lean_inc(v_nextMacroScope_1160_);
lean_inc(v_usedQuotCtxts_1159_);
lean_inc(v_scopes_1158_);
lean_inc(v_messages_1157_);
lean_inc(v_env_1156_);
lean_dec(v___x_1154_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1178_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_asyncMode_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v_asyncMode_1170_ = lean_ctor_get(v_toEnvExtension_1155_, 2);
lean_inc(v_asyncMode_1170_);
lean_dec_ref(v_toEnvExtension_1155_);
v___x_1171_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1149_, v_env_1156_, v_entry_1148_, v_asyncMode_1170_, v___x_1151_);
lean_dec(v_asyncMode_1170_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1171_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_messages_1157_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_scopes_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_usedQuotCtxts_1159_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_nextMacroScope_1160_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_maxRecDepth_1161_);
lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_ngen_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_auxDeclNGen_1163_);
lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_infoState_1164_);
lean_ctor_set(v_reuseFailAlloc_1177_, 9, v_traceState_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 10, v_snapshotTasks_1166_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_st_ref_set(v___y_1153_, v___x_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6___boxed(lean_object* v_mod_1218_, lean_object* v_isMeta_1219_, lean_object* v_hint_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_isMeta_boxed_1224_; lean_object* v_res_1225_; 
v_isMeta_boxed_1224_ = lean_unbox(v_isMeta_1219_);
v_res_1225_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6(v_mod_1218_, v_isMeta_boxed_1224_, v_hint_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__7(lean_object* v___x_1226_, lean_object* v_declName_1227_, lean_object* v_as_1228_, size_t v_sz_1229_, size_t v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1230_, v_sz_1229_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec(v_declName_1227_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_b_1231_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v_modules_1238_; lean_object* v___x_1239_; lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v_toImport_1242_; lean_object* v_module_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1237_ = l_Lean_Environment_header(v___x_1226_);
v_modules_1238_ = lean_ctor_get(v___x_1237_, 3);
lean_inc_ref(v_modules_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1240_ = lean_array_uget_borrowed(v_as_1228_, v_i_1230_);
v___x_1241_ = lean_array_get(v___x_1239_, v_modules_1238_, v_a_1240_);
lean_dec_ref(v_modules_1238_);
v_toImport_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_toImport_1242_);
lean_dec(v___x_1241_);
v_module_1243_ = lean_ctor_get(v_toImport_1242_, 0);
lean_inc(v_module_1243_);
lean_dec_ref(v_toImport_1242_);
v___x_1244_ = 0;
lean_inc(v_declName_1227_);
v___x_1245_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6(v_module_1243_, v___x_1244_, v_declName_1227_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; 
lean_dec_ref(v___x_1245_);
v___x_1246_ = lean_box(0);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1230_, v___x_1247_);
v_i_1230_ = v___x_1248_;
v_b_1231_ = v___x_1246_;
goto _start;
}
else
{
lean_dec(v_declName_1227_);
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__7___boxed(lean_object* v___x_1250_, lean_object* v_declName_1251_, lean_object* v_as_1252_, lean_object* v_sz_1253_, lean_object* v_i_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
size_t v_sz_boxed_1259_; size_t v_i_boxed_1260_; lean_object* v_res_1261_; 
v_sz_boxed_1259_ = lean_unbox_usize(v_sz_1253_);
lean_dec(v_sz_1253_);
v_i_boxed_1260_ = lean_unbox_usize(v_i_1254_);
lean_dec(v_i_1254_);
v_res_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__7(v___x_1250_, v_declName_1251_, v_as_1252_, v_sz_boxed_1259_, v_i_boxed_1260_, v_b_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_as_1252_);
lean_dec_ref(v___x_1250_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_a_1262_, lean_object* v_x_1263_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_a_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg(v_a_1271_, v_x_1272_);
lean_dec(v_x_1272_);
lean_dec(v_a_1271_);
return v_res_1273_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1274_; uint64_t v___x_1275_; 
v___x_1274_ = lean_unsigned_to_nat(1723u);
v___x_1275_ = lean_uint64_of_nat(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_buckets_1278_; lean_object* v___x_1279_; uint64_t v___y_1281_; 
v_buckets_1278_ = lean_ctor_get(v_m_1276_, 1);
v___x_1279_ = lean_array_get_size(v_buckets_1278_);
if (lean_obj_tag(v_a_1277_) == 0)
{
uint64_t v___x_1295_; 
v___x_1295_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___closed__0);
v___y_1281_ = v___x_1295_;
goto v___jp_1280_;
}
else
{
uint64_t v_hash_1296_; 
v_hash_1296_ = lean_ctor_get_uint64(v_a_1277_, sizeof(void*)*2);
v___y_1281_ = v_hash_1296_;
goto v___jp_1280_;
}
v___jp_1280_:
{
uint64_t v___x_1282_; uint64_t v___x_1283_; uint64_t v_fold_1284_; uint64_t v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1282_ = 32ULL;
v___x_1283_ = lean_uint64_shift_right(v___y_1281_, v___x_1282_);
v_fold_1284_ = lean_uint64_xor(v___y_1281_, v___x_1283_);
v___x_1285_ = 16ULL;
v___x_1286_ = lean_uint64_shift_right(v_fold_1284_, v___x_1285_);
v___x_1287_ = lean_uint64_xor(v_fold_1284_, v___x_1286_);
v___x_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = lean_usize_of_nat(v___x_1279_);
v___x_1290_ = ((size_t)1ULL);
v___x_1291_ = lean_usize_sub(v___x_1289_, v___x_1290_);
v___x_1292_ = lean_usize_land(v___x_1288_, v___x_1291_);
v___x_1293_ = lean_array_uget_borrowed(v_buckets_1278_, v___x_1292_);
v___x_1294_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg(v_a_1277_, v___x_1293_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg(v_m_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_m_1297_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__1));
v___x_1303_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__0));
v___x_1304_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1303_, v___x_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_declName_1307_, uint8_t v_isMeta_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1316_; lean_object* v___y_1318_; lean_object* v___x_1331_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_env_1316_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1316_);
lean_dec(v___x_1312_);
v___x_1331_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1316_, v_declName_1307_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_dec_ref(v_env_1316_);
lean_dec(v_declName_1307_);
goto v___jp_1313_;
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1333_; lean_object* v_modules_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_val_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_val_1332_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = l_Lean_Environment_header(v_env_1316_);
v_modules_1334_ = lean_ctor_get(v___x_1333_, 3);
lean_inc_ref(v_modules_1334_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = lean_array_get_size(v_modules_1334_);
v___x_1336_ = lean_nat_dec_lt(v_val_1332_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v_modules_1334_);
lean_dec(v_val_1332_);
lean_dec_ref(v_env_1316_);
lean_dec(v_declName_1307_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1337_; lean_object* v_env_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___y_1342_; 
v___x_1337_ = lean_st_ref_get(v___y_1310_);
v_env_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc_ref(v_env_1338_);
lean_dec(v___x_1337_);
v___x_1339_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__2);
v___x_1340_ = lean_array_fget(v_modules_1334_, v_val_1332_);
lean_dec(v_val_1332_);
lean_dec_ref(v_modules_1334_);
if (v_isMeta_1308_ == 0)
{
lean_dec_ref(v_env_1338_);
v___y_1342_ = v_isMeta_1308_;
goto v___jp_1341_;
}
else
{
uint8_t v___x_1353_; 
lean_inc(v_declName_1307_);
v___x_1353_ = l_Lean_isMarkedMeta(v_env_1338_, v_declName_1307_);
if (v___x_1353_ == 0)
{
v___y_1342_ = v_isMeta_1308_;
goto v___jp_1341_;
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = 0;
v___y_1342_ = v___x_1354_;
goto v___jp_1341_;
}
}
v___jp_1341_:
{
lean_object* v_toImport_1343_; lean_object* v_module_1344_; lean_object* v___x_1345_; 
v_toImport_1343_ = lean_ctor_get(v___x_1340_, 0);
lean_inc_ref(v_toImport_1343_);
lean_dec(v___x_1340_);
v_module_1344_ = lean_ctor_get(v_toImport_1343_, 0);
lean_inc(v_module_1344_);
lean_dec_ref(v_toImport_1343_);
lean_inc(v_declName_1307_);
v___x_1345_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6(v_module_1344_, v___y_1342_, v_declName_1307_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v___x_1345_);
v___x_1346_ = l_Lean_indirectModUseExt;
v___x_1347_ = lean_box(1);
v___x_1348_ = lean_box(0);
lean_inc_ref(v_env_1316_);
v___x_1349_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1339_, v___x_1346_, v_env_1316_, v___x_1347_, v___x_1348_);
v___x_1350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg(v___x_1349_, v_declName_1307_);
lean_dec(v___x_1349_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___closed__3));
v___y_1318_ = v___x_1351_;
goto v___jp_1317_;
}
else
{
lean_object* v_val_1352_; 
v_val_1352_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1352_);
lean_dec_ref(v___x_1350_);
v___y_1318_ = v_val_1352_;
goto v___jp_1317_;
}
}
else
{
lean_dec_ref(v_env_1316_);
lean_dec(v_declName_1307_);
return v___x_1345_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
v___jp_1317_:
{
lean_object* v___x_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_box(0);
v_sz_1320_ = lean_array_size(v___y_1318_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__7(v_env_1316_, v_declName_1307_, v___y_1318_, v_sz_1320_, v___x_1321_, v___x_1319_, v___y_1309_, v___y_1310_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v_env_1316_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1322_, 0);
lean_dec(v_unused_1330_);
v___x_1324_ = v___x_1322_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v___x_1322_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1319_);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1319_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_declName_1355_, lean_object* v_isMeta_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_isMeta_boxed_1360_; lean_object* v_res_1361_; 
v_isMeta_boxed_1360_ = lean_unbox(v_isMeta_1356_);
v_res_1361_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_declName_1355_, v_isMeta_boxed_1360_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg(lean_object* v_as_x27_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
if (lean_obj_tag(v_as_x27_1362_) == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_b_1363_);
return v___x_1367_;
}
else
{
lean_object* v_head_1368_; lean_object* v_tail_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; 
v_head_1368_ = lean_ctor_get(v_as_x27_1362_, 0);
lean_inc(v_head_1368_);
v_tail_1369_ = lean_ctor_get(v_as_x27_1362_, 1);
lean_inc(v_tail_1369_);
lean_dec_ref(v_as_x27_1362_);
v___x_1370_ = 1;
v___x_1371_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_head_1368_, v___x_1370_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v___x_1371_);
v___x_1372_ = lean_box(0);
v_as_x27_1362_ = v_tail_1369_;
v_b_1363_ = v___x_1372_;
goto _start;
}
else
{
lean_dec(v_tail_1369_);
return v___x_1371_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg___boxed(lean_object* v_as_x27_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg(v_as_x27_1374_, v_b_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1380_, lean_object* v_currNamespace_1381_, lean_object* v_openDecls_1382_, lean_object* v_n_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = l_Lean_ResolveName_resolveNamespace(v_env_1380_, v_currNamespace_1381_, v_openDecls_1382_, v_n_1383_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___y_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1388_, lean_object* v_currNamespace_1389_, lean_object* v_openDecls_1390_, lean_object* v_n_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1388_, v_currNamespace_1389_, v_openDecls_1390_, v_n_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_as_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
if (lean_obj_tag(v_as_1395_) == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
else
{
lean_object* v_head_1401_; lean_object* v_tail_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1418_; 
v_head_1401_ = lean_ctor_get(v_as_1395_, 0);
lean_inc(v_head_1401_);
v_tail_1402_ = lean_ctor_get(v_as_1395_, 1);
lean_inc(v_tail_1402_);
lean_dec_ref(v_as_1395_);
v_fst_1403_ = lean_ctor_get(v_head_1401_, 0);
lean_inc(v_fst_1403_);
v_snd_1404_ = lean_ctor_get(v_head_1401_, 1);
lean_inc(v_snd_1404_);
lean_dec(v_head_1401_);
lean_inc(v_fst_1403_);
v___x_1405_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg(v_fst_1403_, v___y_1397_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1418_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1418_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_unbox(v_a_1406_);
lean_dec(v_a_1406_);
if (v___x_1410_ == 0)
{
lean_del_object(v___x_1408_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
v_as_1395_ = v_tail_1402_;
goto _start;
}
else
{
lean_object* v___x_1413_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 3);
lean_ctor_set(v___x_1408_, 0, v_snd_1404_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_snd_1404_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = l_Lean_MessageData_ofFormat(v___x_1413_);
v___x_1415_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_fst_1403_, v___x_1414_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref(v___x_1415_);
v_as_1395_ = v_tail_1402_;
goto _start;
}
else
{
lean_dec(v_tail_1402_);
return v___x_1415_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_as_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_as_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_currNamespace_1424_);
lean_ctor_set(v___x_1427_, 1, v___y_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1428_, v___y_1429_, v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg(lean_object* v_x_1432_, lean_object* v___y_1433_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v_x_1432_, 0);
lean_inc(v_a_1434_);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1434_);
lean_ctor_set(v___x_1435_, 1, v___y_1433_);
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v_x_1432_, 0);
lean_inc(v_a_1436_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1436_);
lean_ctor_set(v___x_1437_, 1, v___y_1433_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg___boxed(lean_object* v_x_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg(v_x_1438_, v___y_1439_);
lean_dec_ref(v_x_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1441_, lean_object* v_stx_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1441_, v_stx_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
if (lean_obj_tag(v_a_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1456_);
v___x_1449_ = v___x_1445_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1445_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_box(0);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_a_1447_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1485_; 
v_val_1457_ = lean_ctor_get(v_a_1446_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_a_1446_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1459_ = v_a_1446_;
v_isShared_1460_ = v_isSharedCheck_1485_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_val_1457_);
lean_dec(v_a_1446_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1485_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v_snd_1461_; 
v_snd_1461_ = lean_ctor_get(v_val_1457_, 1);
lean_inc(v_snd_1461_);
lean_dec(v_val_1457_);
if (lean_obj_tag(v_snd_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1471_; 
lean_del_object(v___x_1459_);
v_a_1462_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1445_);
v_a_1463_ = lean_ctor_get(v_snd_1461_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_snd_1461_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1465_ = v_snd_1461_;
v_isShared_1466_ = v_isSharedCheck_1471_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v_snd_1461_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1471_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg(v___x_1468_, v_a_1462_);
lean_dec_ref(v___x_1468_);
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1484_; 
v_a_1472_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1445_);
v_a_1473_ = lean_ctor_get(v_snd_1461_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_snd_1461_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1475_ = v_snd_1461_;
v_isShared_1476_ = v_isSharedCheck_1484_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v_snd_1461_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1484_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v_a_1473_);
v___x_1478_ = v___x_1459_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1478_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg(v___x_1480_, v_a_1472_);
lean_dec_ref(v___x_1480_);
return v___x_1481_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1486_ = lean_ctor_get(v___x_1445_, 0);
v_a_1487_ = lean_ctor_get(v___x_1445_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1445_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_inc(v_a_1486_);
lean_dec(v___x_1445_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1486_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1495_, lean_object* v_stx_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1495_, v_stx_1496_, v___y_1497_, v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Elab_Command_getRef___redArg(v___y_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v_fileName_1507_; lean_object* v_fileMap_1508_; lean_object* v_currRecDepth_1509_; lean_object* v_cmdPos_1510_; lean_object* v_macroStack_1511_; lean_object* v_quotContext_x3f_1512_; lean_object* v_currMacroScope_1513_; lean_object* v_snap_x3f_1514_; lean_object* v_cancelTk_x3f_1515_; uint8_t v_suppressElabErrors_1516_; lean_object* v_ref_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v_fileName_1507_ = lean_ctor_get(v___y_1502_, 0);
v_fileMap_1508_ = lean_ctor_get(v___y_1502_, 1);
v_currRecDepth_1509_ = lean_ctor_get(v___y_1502_, 2);
v_cmdPos_1510_ = lean_ctor_get(v___y_1502_, 3);
v_macroStack_1511_ = lean_ctor_get(v___y_1502_, 4);
v_quotContext_x3f_1512_ = lean_ctor_get(v___y_1502_, 5);
v_currMacroScope_1513_ = lean_ctor_get(v___y_1502_, 6);
v_snap_x3f_1514_ = lean_ctor_get(v___y_1502_, 8);
v_cancelTk_x3f_1515_ = lean_ctor_get(v___y_1502_, 9);
v_suppressElabErrors_1516_ = lean_ctor_get_uint8(v___y_1502_, sizeof(void*)*10);
v_ref_1517_ = l_Lean_replaceRef(v_ref_1500_, v_a_1506_);
lean_dec(v_a_1506_);
lean_inc(v_cancelTk_x3f_1515_);
lean_inc(v_snap_x3f_1514_);
lean_inc(v_currMacroScope_1513_);
lean_inc(v_quotContext_x3f_1512_);
lean_inc(v_macroStack_1511_);
lean_inc(v_cmdPos_1510_);
lean_inc(v_currRecDepth_1509_);
lean_inc_ref(v_fileMap_1508_);
lean_inc_ref(v_fileName_1507_);
v___x_1518_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1518_, 0, v_fileName_1507_);
lean_ctor_set(v___x_1518_, 1, v_fileMap_1508_);
lean_ctor_set(v___x_1518_, 2, v_currRecDepth_1509_);
lean_ctor_set(v___x_1518_, 3, v_cmdPos_1510_);
lean_ctor_set(v___x_1518_, 4, v_macroStack_1511_);
lean_ctor_set(v___x_1518_, 5, v_quotContext_x3f_1512_);
lean_ctor_set(v___x_1518_, 6, v_currMacroScope_1513_);
lean_ctor_set(v___x_1518_, 7, v_ref_1517_);
lean_ctor_set(v___x_1518_, 8, v_snap_x3f_1514_);
lean_ctor_set(v___x_1518_, 9, v_cancelTk_x3f_1515_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*10, v_suppressElabErrors_1516_);
v___x_1519_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1501_, v___x_1518_, v___y_1503_);
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v_msg_1501_);
v_a_1520_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1505_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1505_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_1528_, v_msg_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v_ref_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v_env_1540_; lean_object* v___x_1541_; lean_object* v_scopes_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_opts_1545_; lean_object* v___x_1546_; 
v___x_1539_ = lean_st_ref_get(v___y_1537_);
v_env_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc_ref(v_env_1540_);
lean_dec(v___x_1539_);
v___x_1541_ = lean_st_ref_get(v___y_1537_);
v_scopes_1542_ = lean_ctor_get(v___x_1541_, 2);
lean_inc(v_scopes_1542_);
lean_dec(v___x_1541_);
v___x_1543_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1544_ = l_List_head_x21___redArg(v___x_1543_, v_scopes_1542_);
lean_dec(v_scopes_1542_);
v_opts_1545_ = lean_ctor_get(v___x_1544_, 1);
lean_inc_ref(v_opts_1545_);
lean_dec(v___x_1544_);
v___x_1546_ = l_Lean_Elab_Command_getScope___redArg(v___y_1537_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_currNamespace_1548_; lean_object* v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v_currNamespace_1548_ = lean_ctor_get(v_a_1547_, 2);
lean_inc(v_currNamespace_1548_);
lean_dec(v_a_1547_);
v___x_1549_ = l_Lean_Elab_Command_getScope___redArg(v___y_1537_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_openDecls_1551_; lean_object* v___x_1552_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v_openDecls_1551_ = lean_ctor_get(v_a_1550_, 3);
lean_inc(v_openDecls_1551_);
lean_dec(v_a_1550_);
v___x_1552_ = l_Lean_Elab_Command_getRef___redArg(v___y_1536_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1536_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v_currRecDepth_1556_; lean_object* v_quotContext_x3f_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___f_1560_; lean_object* v___f_1561_; lean_object* v___f_1562_; lean_object* v_methods_1563_; lean_object* v_a_1565_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v_currRecDepth_1556_ = lean_ctor_get(v___y_1536_, 2);
v_quotContext_x3f_1557_ = lean_ctor_get(v___y_1536_, 5);
lean_inc_ref(v_env_1540_);
v___f_1558_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1558_, 0, v_env_1540_);
lean_inc_ref(v_env_1540_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1559_, 0, v_env_1540_);
lean_inc(v_currNamespace_1548_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1560_, 0, v_currNamespace_1548_);
lean_inc(v_openDecls_1551_);
lean_inc(v_currNamespace_1548_);
lean_inc_ref(v_env_1540_);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1561_, 0, v_env_1540_);
lean_closure_set(v___f_1561_, 1, v_currNamespace_1548_);
lean_closure_set(v___f_1561_, 2, v_openDecls_1551_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1562_, 0, v_env_1540_);
lean_closure_set(v___f_1562_, 1, v_opts_1545_);
lean_closure_set(v___f_1562_, 2, v_currNamespace_1548_);
lean_closure_set(v___f_1562_, 3, v_openDecls_1551_);
v_methods_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1563_, 0, v___f_1559_);
lean_ctor_set(v_methods_1563_, 1, v___f_1560_);
lean_ctor_set(v_methods_1563_, 2, v___f_1558_);
lean_ctor_set(v_methods_1563_, 3, v___f_1561_);
lean_ctor_set(v_methods_1563_, 4, v___f_1562_);
if (lean_obj_tag(v_quotContext_x3f_1557_) == 0)
{
lean_object* v___x_1637_; lean_object* v_a_1638_; 
v___x_1637_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1537_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1637_);
v_a_1565_ = v_a_1638_;
goto v___jp_1564_;
}
else
{
lean_object* v_val_1639_; 
v_val_1639_ = lean_ctor_get(v_quotContext_x3f_1557_, 0);
lean_inc(v_val_1639_);
v_a_1565_ = v_val_1639_;
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1566_; lean_object* v_maxRecDepth_1567_; lean_object* v___x_1568_; lean_object* v_nextMacroScope_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1566_ = lean_st_ref_get(v___y_1537_);
v_maxRecDepth_1567_ = lean_ctor_get(v___x_1566_, 5);
lean_inc(v_maxRecDepth_1567_);
lean_dec(v___x_1566_);
v___x_1568_ = lean_st_ref_get(v___y_1537_);
v_nextMacroScope_1569_ = lean_ctor_get(v___x_1568_, 4);
lean_inc(v_nextMacroScope_1569_);
lean_dec(v___x_1568_);
lean_inc(v_currRecDepth_1556_);
v___x_1570_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1570_, 0, v_methods_1563_);
lean_ctor_set(v___x_1570_, 1, v_a_1565_);
lean_ctor_set(v___x_1570_, 2, v_a_1555_);
lean_ctor_set(v___x_1570_, 3, v_currRecDepth_1556_);
lean_ctor_set(v___x_1570_, 4, v_maxRecDepth_1567_);
lean_ctor_set(v___x_1570_, 5, v_a_1553_);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1572_, 0, v_nextMacroScope_1569_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
lean_ctor_set(v___x_1572_, 2, v___x_1571_);
v___x_1573_ = lean_apply_2(v_x_1535_, v___x_1570_, v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v_a_1575_; lean_object* v_macroScope_1576_; lean_object* v_traceMsgs_1577_; lean_object* v_expandedMacroDecls_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 1);
lean_inc(v_a_1574_);
v_a_1575_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1573_);
v_macroScope_1576_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_macroScope_1576_);
v_traceMsgs_1577_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_traceMsgs_1577_);
v_expandedMacroDecls_1578_ = lean_ctor_get(v_a_1574_, 2);
lean_inc(v_expandedMacroDecls_1578_);
lean_dec(v_a_1574_);
v___x_1579_ = lean_box(0);
v___x_1580_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg(v_expandedMacroDecls_1578_, v___x_1579_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1581_; lean_object* v_env_1582_; lean_object* v_messages_1583_; lean_object* v_scopes_1584_; lean_object* v_usedQuotCtxts_1585_; lean_object* v_maxRecDepth_1586_; lean_object* v_ngen_1587_; lean_object* v_auxDeclNGen_1588_; lean_object* v_infoState_1589_; lean_object* v_traceState_1590_; lean_object* v_snapshotTasks_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v___x_1580_);
v___x_1581_ = lean_st_ref_take(v___y_1537_);
v_env_1582_ = lean_ctor_get(v___x_1581_, 0);
v_messages_1583_ = lean_ctor_get(v___x_1581_, 1);
v_scopes_1584_ = lean_ctor_get(v___x_1581_, 2);
v_usedQuotCtxts_1585_ = lean_ctor_get(v___x_1581_, 3);
v_maxRecDepth_1586_ = lean_ctor_get(v___x_1581_, 5);
v_ngen_1587_ = lean_ctor_get(v___x_1581_, 6);
v_auxDeclNGen_1588_ = lean_ctor_get(v___x_1581_, 7);
v_infoState_1589_ = lean_ctor_get(v___x_1581_, 8);
v_traceState_1590_ = lean_ctor_get(v___x_1581_, 9);
v_snapshotTasks_1591_ = lean_ctor_get(v___x_1581_, 10);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v___x_1581_, 4);
lean_dec(v_unused_1618_);
v___x_1593_ = v___x_1581_;
v_isShared_1594_ = v_isSharedCheck_1617_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snapshotTasks_1591_);
lean_inc(v_traceState_1590_);
lean_inc(v_infoState_1589_);
lean_inc(v_auxDeclNGen_1588_);
lean_inc(v_ngen_1587_);
lean_inc(v_maxRecDepth_1586_);
lean_inc(v_usedQuotCtxts_1585_);
lean_inc(v_scopes_1584_);
lean_inc(v_messages_1583_);
lean_inc(v_env_1582_);
lean_dec(v___x_1581_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1617_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v_macroScope_1576_);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_env_1582_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_messages_1583_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_scopes_1584_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_usedQuotCtxts_1585_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_macroScope_1576_);
lean_ctor_set(v_reuseFailAlloc_1616_, 5, v_maxRecDepth_1586_);
lean_ctor_set(v_reuseFailAlloc_1616_, 6, v_ngen_1587_);
lean_ctor_set(v_reuseFailAlloc_1616_, 7, v_auxDeclNGen_1588_);
lean_ctor_set(v_reuseFailAlloc_1616_, 8, v_infoState_1589_);
lean_ctor_set(v_reuseFailAlloc_1616_, 9, v_traceState_1590_);
lean_ctor_set(v_reuseFailAlloc_1616_, 10, v_snapshotTasks_1591_);
v___x_1596_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_st_ref_set(v___y_1537_, v___x_1596_);
v___x_1598_ = l_List_reverse___redArg(v_traceMsgs_1577_);
v___x_1599_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v___x_1598_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___y_1536_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v___x_1599_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v___x_1599_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_a_1575_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1575_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1575_);
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_traceMsgs_1577_);
lean_dec(v_macroScope_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v___y_1536_);
v_a_1619_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1580_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1580_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_a_1627_; 
v_a_1627_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1573_);
if (lean_obj_tag(v_a_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v_a_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_a_1628_ = lean_ctor_get(v_a_1627_, 0);
lean_inc(v_a_1628_);
v_a_1629_ = lean_ctor_get(v_a_1627_, 1);
lean_inc_ref(v_a_1629_);
lean_dec_ref(v_a_1627_);
v___x_1630_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1631_ = lean_string_dec_eq(v_a_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_a_1629_);
v___x_1633_ = l_Lean_MessageData_ofFormat(v___x_1632_);
v___x_1634_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1628_, v___x_1633_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_a_1628_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; 
lean_dec_ref(v_a_1629_);
lean_dec_ref(v___y_1536_);
v___x_1635_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(v_a_1628_);
return v___x_1635_;
}
}
else
{
lean_object* v___x_1636_; 
lean_dec_ref(v___y_1536_);
v___x_1636_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_a_1553_);
lean_dec(v_openDecls_1551_);
lean_dec(v_currNamespace_1548_);
lean_dec_ref(v_opts_1545_);
lean_dec_ref(v_env_1540_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_x_1535_);
v_a_1640_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1554_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1554_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_openDecls_1551_);
lean_dec(v_currNamespace_1548_);
lean_dec_ref(v_opts_1545_);
lean_dec_ref(v_env_1540_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_x_1535_);
v_a_1648_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1552_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1552_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_currNamespace_1548_);
lean_dec_ref(v_opts_1545_);
lean_dec_ref(v_env_1540_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_x_1535_);
v_a_1656_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1549_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1549_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v_opts_1545_);
lean_dec_ref(v_env_1540_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_x_1535_);
v_a_1664_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1546_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1546_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
return v_res_1676_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1691_ = l_String_toRawSubstring_x27(v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1715_ = lean_unsigned_to_nat(14u);
v___x_1716_ = lean_unsigned_to_nat(22u);
v___x_1717_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1718_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1719_ = l_mkPanicMessageWithDecl(v___x_1718_, v___x_1717_, v___x_1716_, v___x_1715_, v___x_1714_);
return v___x_1719_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1736_ = l_String_toRawSubstring_x27(v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1749_ = l_Lean_mkAtom(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1752_ = l_Lean_mkAtom(v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1753_, lean_object* v_id_1754_, lean_object* v_stx_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_pat_1760_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1755_);
v___x_1764_ = l_Lean_Syntax_isOfKind(v_stx_1755_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1755_);
v___x_1766_ = l_Lean_Syntax_isOfKind(v_stx_1755_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v_a_1773_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v_a_1809_; uint8_t v___x_1840_; 
v___x_1767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1755_);
v___x_1840_ = l_Lean_Syntax_isOfKind(v_stx_1755_, v___x_1767_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1755_);
v___x_1842_ = l_Lean_Syntax_isOfKind(v_stx_1755_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1755_);
v___x_1844_ = l_Lean_Syntax_isOfKind(v_stx_1755_, v___x_1843_);
if (v___x_1844_ == 0)
{
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_quotContext_x3f_1849_; lean_object* v___x_1850_; lean_object* v_a_1852_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v_quotContext_x3f_1849_ = lean_ctor_get(v_a_1756_, 5);
v___x_1850_ = l_Lean_SourceInfo_fromRef(v_a_1846_, v___x_1844_);
lean_dec(v_a_1846_);
if (lean_obj_tag(v_quotContext_x3f_1849_) == 0)
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v_a_1852_ = v_a_1884_;
goto v___jp_1851_;
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v___x_1850_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_1885_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1883_);
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
lean_object* v_val_1893_; 
v_val_1893_ = lean_ctor_get(v_quotContext_x3f_1849_, 0);
lean_inc(v_val_1893_);
v_a_1852_ = v_val_1893_;
goto v___jp_1851_;
}
v___jp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1853_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1854_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1855_ = l_Lean_addMacroScope(v_a_1852_, v___x_1854_, v_a_1848_);
v___x_1856_ = lean_box(0);
lean_inc(v___x_1850_);
v___x_1857_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1850_);
lean_ctor_set(v___x_1857_, 1, v___x_1853_);
lean_ctor_set(v___x_1857_, 2, v___x_1855_);
lean_ctor_set(v___x_1857_, 3, v___x_1856_);
v___x_1858_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_1850_);
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1850_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_1850_);
v___x_1861_ = l_Lean_Syntax_node1(v___x_1850_, v___x_1860_, v_stx_1755_);
v___x_1862_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1874_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1874_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1874_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1850_);
v___x_1868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1850_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_Syntax_node4(v___x_1850_, v___x_1767_, v___x_1857_, v___x_1859_, v___x_1861_, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1870_);
v___x_1872_ = v___x_1865_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v___x_1861_);
lean_dec_ref(v___x_1859_);
lean_dec_ref(v___x_1857_);
lean_dec(v___x_1850_);
v_a_1875_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1862_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1862_);
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
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_1894_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1847_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1847_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_1902_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1845_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1845_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_val_1910_; lean_object* v___x_1911_; 
lean_dec(v_id_1754_);
v_val_1910_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_1910_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_1911_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_1910_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v_pat_1760_ = v_a_1912_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_stx_1755_);
v_a_1913_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1911_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_1921_);
lean_inc(v___x_1922_);
v___x_1923_ = l_Lean_Syntax_matchesNull(v___x_1922_, v___x_1921_);
if (v___x_1923_ == 0)
{
lean_dec(v___x_1922_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v_quotContext_x3f_1928_; lean_object* v___x_1929_; lean_object* v_a_1931_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v_quotContext_x3f_1928_ = lean_ctor_get(v_a_1756_, 5);
v___x_1929_ = l_Lean_SourceInfo_fromRef(v_a_1925_, v___x_1923_);
lean_dec(v_a_1925_);
if (lean_obj_tag(v_quotContext_x3f_1928_) == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v_a_1931_ = v_a_1963_;
goto v___jp_1930_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v___x_1929_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_1964_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1962_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1962_);
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
lean_object* v_val_1972_; 
v_val_1972_ = lean_ctor_get(v_quotContext_x3f_1928_, 0);
lean_inc(v_val_1972_);
v_a_1931_ = v_val_1972_;
goto v___jp_1930_;
}
v___jp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1932_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1934_ = l_Lean_addMacroScope(v_a_1931_, v___x_1933_, v_a_1927_);
v___x_1935_ = lean_box(0);
lean_inc(v___x_1929_);
v___x_1936_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1929_);
lean_ctor_set(v___x_1936_, 1, v___x_1932_);
lean_ctor_set(v___x_1936_, 2, v___x_1934_);
lean_ctor_set(v___x_1936_, 3, v___x_1935_);
v___x_1937_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_1929_);
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1929_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_1929_);
v___x_1940_ = l_Lean_Syntax_node1(v___x_1929_, v___x_1939_, v_stx_1755_);
v___x_1941_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1953_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1953_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1953_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1946_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1929_);
v___x_1947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1929_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = l_Lean_Syntax_node4(v___x_1929_, v___x_1767_, v___x_1936_, v___x_1938_, v___x_1940_, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v_a_1942_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1949_);
v___x_1951_ = v___x_1944_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v___x_1940_);
lean_dec_ref(v___x_1938_);
lean_dec_ref(v___x_1936_);
lean_dec(v___x_1929_);
v_a_1954_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1941_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1941_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_1973_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1926_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1926_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_1981_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1924_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1924_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_val_1989_; lean_object* v___x_1990_; 
lean_dec(v_id_1754_);
v_val_1989_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_1989_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_1990_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_1989_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref(v___x_1990_);
v_pat_1760_ = v_a_1991_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_stx_1755_);
v_a_1992_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1990_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2000_ = lean_unsigned_to_nat(3u);
v___x_2001_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2000_);
v___x_2002_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2001_);
v___x_2003_ = l_Lean_Syntax_isOfKind(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_dec(v___x_2001_);
lean_dec(v___x_1922_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_quotContext_x3f_2008_; lean_object* v___x_2009_; lean_object* v_a_2011_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v_quotContext_x3f_2008_ = lean_ctor_get(v_a_1756_, 5);
v___x_2009_ = l_Lean_SourceInfo_fromRef(v_a_2005_, v___x_2003_);
lean_dec(v_a_2005_);
if (lean_obj_tag(v_quotContext_x3f_2008_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
v_a_2011_ = v_a_2043_;
goto v___jp_2010_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v___x_2009_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2044_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2042_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2042_);
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
lean_object* v_val_2052_; 
v_val_2052_ = lean_ctor_get(v_quotContext_x3f_2008_, 0);
lean_inc(v_val_2052_);
v_a_2011_ = v_val_2052_;
goto v___jp_2010_;
}
v___jp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2012_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2013_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2014_ = l_Lean_addMacroScope(v_a_2011_, v___x_2013_, v_a_2007_);
v___x_2015_ = lean_box(0);
lean_inc(v___x_2009_);
v___x_2016_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2009_);
lean_ctor_set(v___x_2016_, 1, v___x_2012_);
lean_ctor_set(v___x_2016_, 2, v___x_2014_);
lean_ctor_set(v___x_2016_, 3, v___x_2015_);
v___x_2017_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2009_);
v___x_2018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2009_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2009_);
v___x_2020_ = l_Lean_Syntax_node1(v___x_2009_, v___x_2019_, v_stx_1755_);
v___x_2021_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2033_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2026_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2009_);
v___x_2027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2009_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = l_Lean_Syntax_node4(v___x_2009_, v___x_1767_, v___x_2016_, v___x_2018_, v___x_2020_, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v_a_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2029_);
v___x_2031_ = v___x_2024_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v___x_2020_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2009_);
v_a_2034_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2021_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2021_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2005_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2053_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2006_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2006_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2061_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2004_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2004_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_val_2069_; lean_object* v___x_2070_; 
lean_dec(v_id_1754_);
v_val_2069_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2069_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2070_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2069_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2070_);
v_pat_1760_ = v_a_2071_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_stx_1755_);
v_a_2072_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2070_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2070_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v_stx_2081_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2107_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v_stx_2081_ = l_Lean_Syntax_getArg(v___x_1922_, v___x_2080_);
lean_dec(v___x_1922_);
v___x_2107_ = lean_unsigned_to_nat(2u);
v___x_2159_ = lean_unsigned_to_nat(4u);
v___x_2160_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2159_);
v___x_2161_ = l_Lean_Syntax_isNone(v___x_2160_);
if (v___x_2161_ == 0)
{
uint8_t v___x_2162_; 
lean_inc(v___x_2160_);
v___x_2162_ = l_Lean_Syntax_matchesNull(v___x_2160_, v___x_2107_);
if (v___x_2162_ == 0)
{
lean_dec(v___x_2160_);
lean_dec(v_stx_2081_);
lean_dec(v___x_2001_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v_quotContext_x3f_2167_; lean_object* v___x_2168_; lean_object* v_a_2170_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2165_);
v_quotContext_x3f_2167_ = lean_ctor_get(v_a_1756_, 5);
v___x_2168_ = l_Lean_SourceInfo_fromRef(v_a_2164_, v___x_1842_);
lean_dec(v_a_2164_);
if (lean_obj_tag(v_quotContext_x3f_2167_) == 0)
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v_a_2170_ = v_a_2202_;
goto v___jp_2169_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v___x_2168_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2203_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2201_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2201_);
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
lean_object* v_val_2211_; 
v_val_2211_ = lean_ctor_get(v_quotContext_x3f_2167_, 0);
lean_inc(v_val_2211_);
v_a_2170_ = v_val_2211_;
goto v___jp_2169_;
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2171_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2172_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2173_ = l_Lean_addMacroScope(v_a_2170_, v___x_2172_, v_a_2166_);
v___x_2174_ = lean_box(0);
lean_inc(v___x_2168_);
v___x_2175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2168_);
lean_ctor_set(v___x_2175_, 1, v___x_2171_);
lean_ctor_set(v___x_2175_, 2, v___x_2173_);
lean_ctor_set(v___x_2175_, 3, v___x_2174_);
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2168_);
v___x_2177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2168_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2168_);
v___x_2179_ = l_Lean_Syntax_node1(v___x_2168_, v___x_2178_, v_stx_1755_);
v___x_2180_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2192_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2192_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2192_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2168_);
v___x_2186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2168_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_Syntax_node4(v___x_2168_, v___x_1767_, v___x_2175_, v___x_2177_, v___x_2179_, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v_a_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2188_);
v___x_2190_ = v___x_2183_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v___x_2179_);
lean_dec_ref(v___x_2177_);
lean_dec_ref(v___x_2175_);
lean_dec(v___x_2168_);
v_a_2193_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2180_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2180_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2164_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2212_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2165_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2165_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2220_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2163_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2163_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v_val_2228_; lean_object* v___x_2229_; 
lean_dec(v_id_1754_);
v_val_2228_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2228_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2229_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2228_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v_pat_1760_ = v_a_2230_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_stx_1755_);
v_a_2231_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2229_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2229_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = l_Lean_Syntax_getArg(v___x_2160_, v___x_1921_);
lean_dec(v___x_2160_);
v___x_2240_ = l_Lean_Syntax_matchesNull(v___x_2239_, v___x_1921_);
if (v___x_2240_ == 0)
{
lean_dec(v_stx_2081_);
lean_dec(v___x_2001_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2243_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v_quotContext_x3f_2245_; lean_object* v___x_2246_; lean_object* v_a_2248_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v_quotContext_x3f_2245_ = lean_ctor_get(v_a_1756_, 5);
v___x_2246_ = l_Lean_SourceInfo_fromRef(v_a_2242_, v___x_1842_);
lean_dec(v_a_2242_);
if (lean_obj_tag(v_quotContext_x3f_2245_) == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v_a_2248_ = v_a_2280_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v___x_2246_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2281_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2279_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2279_);
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
lean_object* v_val_2289_; 
v_val_2289_ = lean_ctor_get(v_quotContext_x3f_2245_, 0);
lean_inc(v_val_2289_);
v_a_2248_ = v_val_2289_;
goto v___jp_2247_;
}
v___jp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2249_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2251_ = l_Lean_addMacroScope(v_a_2248_, v___x_2250_, v_a_2244_);
v___x_2252_ = lean_box(0);
lean_inc(v___x_2246_);
v___x_2253_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2246_);
lean_ctor_set(v___x_2253_, 1, v___x_2249_);
lean_ctor_set(v___x_2253_, 2, v___x_2251_);
lean_ctor_set(v___x_2253_, 3, v___x_2252_);
v___x_2254_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2246_);
v___x_2255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2246_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2246_);
v___x_2257_ = l_Lean_Syntax_node1(v___x_2246_, v___x_2256_, v_stx_1755_);
v___x_2258_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2270_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2270_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2270_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2246_);
v___x_2264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2246_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = l_Lean_Syntax_node4(v___x_2246_, v___x_1767_, v___x_2253_, v___x_2255_, v___x_2257_, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v_a_2259_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2266_);
v___x_2268_ = v___x_2261_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2255_);
lean_dec_ref(v___x_2253_);
lean_dec(v___x_2246_);
v_a_2271_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2258_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2258_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2242_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2290_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2243_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2243_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2298_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2241_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2241_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_val_2306_; lean_object* v___x_2307_; 
lean_dec(v_id_1754_);
v_val_2306_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2306_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2307_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2306_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v_pat_1760_ = v_a_2308_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_stx_1755_);
v_a_2309_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2307_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
else
{
v___y_2109_ = v_a_1756_;
v___y_2110_ = v_a_1757_;
goto v___jp_2108_;
}
}
}
else
{
lean_dec(v___x_2160_);
v___y_2109_ = v_a_1756_;
v___y_2110_ = v_a_1757_;
goto v___jp_2108_;
}
v___jp_2082_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2088_ = lean_string_append(v___y_2086_, v___x_2087_);
v___x_2089_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2085_, v_stx_2081_, v_id_1754_, v___x_2088_, v___y_2083_, v___y_2084_);
lean_dec_ref(v___y_2083_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
v_pat_1760_ = v_a_2090_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_stx_1755_);
v_a_2091_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2089_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2089_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
v___jp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2103_ = l_Lean_Syntax_isStrLit_x3f(v___x_2001_);
lean_dec(v___x_2001_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2105_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2104_);
v___y_2083_ = v___y_2100_;
v___y_2084_ = v___y_2101_;
v___y_2085_ = v___x_2102_;
v___y_2086_ = v___x_2105_;
goto v___jp_2082_;
}
else
{
lean_object* v_val_2106_; 
v_val_2106_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_val_2106_);
lean_dec_ref(v___x_2103_);
v___y_2083_ = v___y_2100_;
v___y_2084_ = v___y_2101_;
v___y_2085_ = v___x_2102_;
v___y_2086_ = v_val_2106_;
goto v___jp_2082_;
}
}
v___jp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_unsigned_to_nat(5u);
v___x_2112_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2111_);
v___x_2113_ = l_Lean_Syntax_isNone(v___x_2112_);
if (v___x_2113_ == 0)
{
uint8_t v___x_2114_; 
v___x_2114_ = l_Lean_Syntax_matchesNull(v___x_2112_, v___x_2107_);
if (v___x_2114_ == 0)
{
lean_dec(v_stx_2081_);
lean_dec(v___x_2001_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Elab_Command_getRef___redArg(v___y_2109_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2109_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v_quotContext_x3f_2119_; lean_object* v___x_2120_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v_quotContext_x3f_2119_ = lean_ctor_get(v___y_2109_, 5);
v___x_2120_ = l_Lean_SourceInfo_fromRef(v_a_2116_, v___x_1842_);
lean_dec(v_a_2116_);
if (lean_obj_tag(v_quotContext_x3f_2119_) == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2110_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2121_);
v___y_1769_ = v___y_2110_;
v___y_1770_ = v_a_2118_;
v___y_1771_ = v___x_2120_;
v___y_1772_ = v___y_2109_;
v_a_1773_ = v_a_2122_;
goto v___jp_1768_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v___x_2120_);
lean_dec(v_a_2118_);
lean_dec_ref(v___y_2109_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2123_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2121_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2121_);
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
lean_object* v_val_2131_; 
v_val_2131_ = lean_ctor_get(v_quotContext_x3f_2119_, 0);
lean_inc(v_val_2131_);
v___y_1769_ = v___y_2110_;
v___y_1770_ = v_a_2118_;
v___y_1771_ = v___x_2120_;
v___y_1772_ = v___y_2109_;
v_a_1773_ = v_val_2131_;
goto v___jp_1768_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_a_2116_);
lean_dec_ref(v___y_2109_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2132_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2117_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2117_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v___y_2109_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2140_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2115_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2115_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_val_2148_; lean_object* v___x_2149_; 
lean_dec(v_id_1754_);
v_val_2148_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2148_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2149_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2148_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___y_2109_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2149_);
v_pat_1760_ = v_a_2150_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_stx_1755_);
v_a_2151_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2149_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2149_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1753_);
v___y_2100_ = v___y_2109_;
v___y_2101_ = v___y_2110_;
goto v___jp_2099_;
}
}
else
{
lean_dec(v___x_2112_);
lean_dec(v_id_x3f_1753_);
v___y_2100_ = v___y_2109_;
v___y_2101_ = v___y_2110_;
goto v___jp_2099_;
}
}
}
}
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2317_);
lean_inc(v___x_2318_);
v___x_2319_ = l_Lean_Syntax_matchesNull(v___x_2318_, v___x_2317_);
if (v___x_2319_ == 0)
{
lean_dec(v___x_2318_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v_quotContext_x3f_2324_; lean_object* v___x_2325_; lean_object* v_a_2327_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2322_);
v_quotContext_x3f_2324_ = lean_ctor_get(v_a_1756_, 5);
v___x_2325_ = l_Lean_SourceInfo_fromRef(v_a_2321_, v___x_2319_);
lean_dec(v_a_2321_);
if (lean_obj_tag(v_quotContext_x3f_2324_) == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v_a_2327_ = v_a_2359_;
goto v___jp_2326_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v___x_2325_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2360_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2358_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2358_);
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
lean_object* v_val_2368_; 
v_val_2368_ = lean_ctor_get(v_quotContext_x3f_2324_, 0);
lean_inc(v_val_2368_);
v_a_2327_ = v_val_2368_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2328_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2329_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2330_ = l_Lean_addMacroScope(v_a_2327_, v___x_2329_, v_a_2323_);
v___x_2331_ = lean_box(0);
lean_inc(v___x_2325_);
v___x_2332_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2325_);
lean_ctor_set(v___x_2332_, 1, v___x_2328_);
lean_ctor_set(v___x_2332_, 2, v___x_2330_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2325_);
v___x_2334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2325_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2325_);
v___x_2336_ = l_Lean_Syntax_node1(v___x_2325_, v___x_2335_, v_stx_1755_);
v___x_2337_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2349_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2325_);
v___x_2343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2325_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = l_Lean_Syntax_node4(v___x_2325_, v___x_1767_, v___x_2332_, v___x_2334_, v___x_2336_, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v_a_2338_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2345_);
v___x_2347_ = v___x_2340_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v___x_2336_);
lean_dec_ref(v___x_2334_);
lean_dec_ref(v___x_2332_);
lean_dec(v___x_2325_);
v_a_2350_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2337_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2337_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2321_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2369_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2322_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2322_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2377_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2320_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2320_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_val_2385_; lean_object* v___x_2386_; 
lean_dec(v_id_1754_);
v_val_2385_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2385_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2386_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2385_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref(v___x_2386_);
v_pat_1760_ = v_a_2387_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_stx_1755_);
v_a_2388_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2386_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2396_ = lean_unsigned_to_nat(3u);
v___x_2397_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2397_);
v___x_2399_ = l_Lean_Syntax_isOfKind(v___x_2397_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec(v___x_2397_);
lean_dec(v___x_2318_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_quotContext_x3f_2404_; lean_object* v___x_2405_; lean_object* v_a_2407_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v_quotContext_x3f_2404_ = lean_ctor_get(v_a_1756_, 5);
v___x_2405_ = l_Lean_SourceInfo_fromRef(v_a_2401_, v___x_2399_);
lean_dec(v_a_2401_);
if (lean_obj_tag(v_quotContext_x3f_2404_) == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
v_a_2407_ = v_a_2439_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v___x_2405_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2440_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2438_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2438_);
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
lean_object* v_val_2448_; 
v_val_2448_ = lean_ctor_get(v_quotContext_x3f_2404_, 0);
lean_inc(v_val_2448_);
v_a_2407_ = v_val_2448_;
goto v___jp_2406_;
}
v___jp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2408_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2409_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2410_ = l_Lean_addMacroScope(v_a_2407_, v___x_2409_, v_a_2403_);
v___x_2411_ = lean_box(0);
lean_inc(v___x_2405_);
v___x_2412_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2405_);
lean_ctor_set(v___x_2412_, 1, v___x_2408_);
lean_ctor_set(v___x_2412_, 2, v___x_2410_);
lean_ctor_set(v___x_2412_, 3, v___x_2411_);
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2405_);
v___x_2414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2405_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2405_);
v___x_2416_ = l_Lean_Syntax_node1(v___x_2405_, v___x_2415_, v_stx_1755_);
v___x_2417_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2429_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2405_);
v___x_2423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2405_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_Syntax_node4(v___x_2405_, v___x_1767_, v___x_2412_, v___x_2414_, v___x_2416_, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2425_);
v___x_2427_ = v___x_2420_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v___x_2416_);
lean_dec_ref(v___x_2414_);
lean_dec_ref(v___x_2412_);
lean_dec(v___x_2405_);
v_a_2430_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2417_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2417_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_a_2401_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2449_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2402_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2402_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2457_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2400_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2400_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2466_; 
lean_dec(v_id_1754_);
v_val_2465_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2465_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2466_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2465_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref(v___x_2466_);
v_pat_1760_ = v_a_2467_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_stx_1755_);
v_a_2468_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2466_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
else
{
lean_object* v___x_2476_; lean_object* v_stx_2477_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2503_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2476_ = lean_unsigned_to_nat(0u);
v_stx_2477_ = l_Lean_Syntax_getArg(v___x_2318_, v___x_2476_);
lean_dec(v___x_2318_);
v___x_2503_ = lean_unsigned_to_nat(2u);
v___x_2555_ = lean_unsigned_to_nat(4u);
v___x_2556_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_isNone(v___x_2556_);
if (v___x_2557_ == 0)
{
uint8_t v___x_2558_; 
lean_inc(v___x_2556_);
v___x_2558_ = l_Lean_Syntax_matchesNull(v___x_2556_, v___x_2503_);
if (v___x_2558_ == 0)
{
lean_dec(v___x_2556_);
lean_dec(v_stx_2477_);
lean_dec(v___x_2397_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v_quotContext_x3f_2563_; lean_object* v___x_2564_; lean_object* v_a_2566_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref(v___x_2561_);
v_quotContext_x3f_2563_ = lean_ctor_get(v_a_1756_, 5);
v___x_2564_ = l_Lean_SourceInfo_fromRef(v_a_2560_, v___x_1840_);
lean_dec(v_a_2560_);
if (lean_obj_tag(v_quotContext_x3f_2563_) == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2597_);
v_a_2566_ = v_a_2598_;
goto v___jp_2565_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v___x_2564_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2599_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2597_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2597_);
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
lean_object* v_val_2607_; 
v_val_2607_ = lean_ctor_get(v_quotContext_x3f_2563_, 0);
lean_inc(v_val_2607_);
v_a_2566_ = v_val_2607_;
goto v___jp_2565_;
}
v___jp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2567_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2568_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2569_ = l_Lean_addMacroScope(v_a_2566_, v___x_2568_, v_a_2562_);
v___x_2570_ = lean_box(0);
lean_inc(v___x_2564_);
v___x_2571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2564_);
lean_ctor_set(v___x_2571_, 1, v___x_2567_);
lean_ctor_set(v___x_2571_, 2, v___x_2569_);
lean_ctor_set(v___x_2571_, 3, v___x_2570_);
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2564_);
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2564_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2564_);
v___x_2575_ = l_Lean_Syntax_node1(v___x_2564_, v___x_2574_, v_stx_1755_);
v___x_2576_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2581_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2564_);
v___x_2582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2564_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node4(v___x_2564_, v___x_1767_, v___x_2571_, v___x_2573_, v___x_2575_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_a_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
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
lean_dec(v___x_2575_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2571_);
lean_dec(v___x_2564_);
v_a_2589_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2576_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2576_);
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
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_a_2560_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2608_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2561_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2561_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2616_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2559_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2559_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2625_; 
lean_dec(v_id_1754_);
v_val_2624_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2624_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2625_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2624_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref(v___x_2625_);
v_pat_1760_ = v_a_2626_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_stx_1755_);
v_a_2627_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2625_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2625_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
else
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = l_Lean_Syntax_getArg(v___x_2556_, v___x_2317_);
lean_dec(v___x_2556_);
v___x_2636_ = l_Lean_Syntax_matchesNull(v___x_2635_, v___x_2317_);
if (v___x_2636_ == 0)
{
lean_dec(v_stx_2477_);
lean_dec(v___x_2397_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_quotContext_x3f_2641_; lean_object* v___x_2642_; lean_object* v_a_2644_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
v_quotContext_x3f_2641_ = lean_ctor_get(v_a_1756_, 5);
v___x_2642_ = l_Lean_SourceInfo_fromRef(v_a_2638_, v___x_1840_);
lean_dec(v_a_2638_);
if (lean_obj_tag(v_quotContext_x3f_2641_) == 0)
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v_a_2644_ = v_a_2676_;
goto v___jp_2643_;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v___x_2642_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2677_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2675_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2675_);
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
lean_object* v_val_2685_; 
v_val_2685_ = lean_ctor_get(v_quotContext_x3f_2641_, 0);
lean_inc(v_val_2685_);
v_a_2644_ = v_val_2685_;
goto v___jp_2643_;
}
v___jp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2645_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2646_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2647_ = l_Lean_addMacroScope(v_a_2644_, v___x_2646_, v_a_2640_);
v___x_2648_ = lean_box(0);
lean_inc(v___x_2642_);
v___x_2649_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2642_);
lean_ctor_set(v___x_2649_, 1, v___x_2645_);
lean_ctor_set(v___x_2649_, 2, v___x_2647_);
lean_ctor_set(v___x_2649_, 3, v___x_2648_);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2642_);
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2642_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2642_);
v___x_2653_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2652_, v_stx_1755_);
v___x_2654_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2666_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2659_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2642_);
v___x_2660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2642_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = l_Lean_Syntax_node4(v___x_2642_, v___x_1767_, v___x_2649_, v___x_2651_, v___x_2653_, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v_a_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2662_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v___x_2653_);
lean_dec_ref(v___x_2651_);
lean_dec_ref(v___x_2649_);
lean_dec(v___x_2642_);
v_a_2667_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2654_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2654_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2638_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2686_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2639_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2639_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2694_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2637_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2637_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_val_2702_; lean_object* v___x_2703_; 
lean_dec(v_id_1754_);
v_val_2702_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2702_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2703_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2702_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref(v___x_2703_);
v_pat_1760_ = v_a_2704_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_stx_1755_);
v_a_2705_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2703_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2703_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
else
{
v___y_2505_ = v_a_1756_;
v___y_2506_ = v_a_1757_;
goto v___jp_2504_;
}
}
}
else
{
lean_dec(v___x_2556_);
v___y_2505_ = v_a_1756_;
v___y_2506_ = v_a_1757_;
goto v___jp_2504_;
}
v___jp_2478_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2484_ = lean_string_append(v___y_2482_, v___x_2483_);
v___x_2485_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2480_, v_stx_2477_, v_id_1754_, v___x_2484_, v___y_2481_, v___y_2479_);
lean_dec_ref(v___y_2481_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref(v___x_2485_);
v_pat_1760_ = v_a_2486_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_stx_1755_);
v_a_2487_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2485_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2485_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
v___jp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2499_ = l_Lean_Syntax_isStrLit_x3f(v___x_2397_);
lean_dec(v___x_2397_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2501_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2500_);
v___y_2479_ = v___y_2497_;
v___y_2480_ = v___x_2498_;
v___y_2481_ = v___y_2496_;
v___y_2482_ = v___x_2501_;
goto v___jp_2478_;
}
else
{
lean_object* v_val_2502_; 
v_val_2502_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_val_2502_);
lean_dec_ref(v___x_2499_);
v___y_2479_ = v___y_2497_;
v___y_2480_ = v___x_2498_;
v___y_2481_ = v___y_2496_;
v___y_2482_ = v_val_2502_;
goto v___jp_2478_;
}
}
v___jp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2507_ = lean_unsigned_to_nat(5u);
v___x_2508_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2507_);
v___x_2509_ = l_Lean_Syntax_isNone(v___x_2508_);
if (v___x_2509_ == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = l_Lean_Syntax_matchesNull(v___x_2508_, v___x_2503_);
if (v___x_2510_ == 0)
{
lean_dec(v_stx_2477_);
lean_dec(v___x_2397_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Elab_Command_getRef___redArg(v___y_2505_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2505_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v_quotContext_x3f_2515_; lean_object* v___x_2516_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2513_);
v_quotContext_x3f_2515_ = lean_ctor_get(v___y_2505_, 5);
v___x_2516_ = l_Lean_SourceInfo_fromRef(v_a_2512_, v___x_1840_);
lean_dec(v_a_2512_);
if (lean_obj_tag(v_quotContext_x3f_2515_) == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2506_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v___x_2517_);
v___y_1805_ = v_a_2514_;
v___y_1806_ = v___x_2516_;
v___y_1807_ = v___y_2505_;
v___y_1808_ = v___y_2506_;
v_a_1809_ = v_a_2518_;
goto v___jp_1804_;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v___x_2516_);
lean_dec(v_a_2514_);
lean_dec_ref(v___y_2505_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2519_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2517_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2517_);
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
lean_object* v_val_2527_; 
v_val_2527_ = lean_ctor_get(v_quotContext_x3f_2515_, 0);
lean_inc(v_val_2527_);
v___y_1805_ = v_a_2514_;
v___y_1806_ = v___x_2516_;
v___y_1807_ = v___y_2505_;
v___y_1808_ = v___y_2506_;
v_a_1809_ = v_val_2527_;
goto v___jp_1804_;
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2512_);
lean_dec_ref(v___y_2505_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2528_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2513_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2513_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v___y_2505_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2536_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2511_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2511_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_val_2544_; lean_object* v___x_2545_; 
lean_dec(v_id_1754_);
v_val_2544_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2544_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2545_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2544_, v___y_2505_, v___y_2506_);
lean_dec_ref(v___y_2505_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2545_);
v_pat_1760_ = v_a_2546_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_stx_1755_);
v_a_2547_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2545_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2545_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1753_);
v___y_2496_ = v___y_2505_;
v___y_2497_ = v___y_2506_;
goto v___jp_2495_;
}
}
else
{
lean_dec(v___x_2508_);
lean_dec(v_id_x3f_1753_);
v___y_2496_ = v___y_2505_;
v___y_2497_ = v___y_2506_;
goto v___jp_2495_;
}
}
}
}
}
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2713_);
v___x_2715_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2716_ = l_Lean_Syntax_matchesIdent(v___x_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2718_ = l_Lean_Syntax_matchesIdent(v___x_2714_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2720_ = l_Lean_Syntax_matchesIdent(v___x_2714_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2722_ = l_Lean_Syntax_matchesIdent(v___x_2714_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2724_ = l_Lean_Syntax_matchesIdent(v___x_2714_, v___x_2723_);
lean_dec(v___x_2714_);
if (v___x_2724_ == 0)
{
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref(v___x_2725_);
v___x_2727_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v_quotContext_x3f_2729_; lean_object* v___x_2730_; lean_object* v_a_2732_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref(v___x_2727_);
v_quotContext_x3f_2729_ = lean_ctor_get(v_a_1756_, 5);
v___x_2730_ = l_Lean_SourceInfo_fromRef(v_a_2726_, v___x_2724_);
lean_dec(v_a_2726_);
if (lean_obj_tag(v_quotContext_x3f_2729_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref(v___x_2763_);
v_a_2732_ = v_a_2764_;
goto v___jp_2731_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v___x_2730_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2765_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2763_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2763_);
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
lean_object* v_val_2773_; 
v_val_2773_ = lean_ctor_get(v_quotContext_x3f_2729_, 0);
lean_inc(v_val_2773_);
v_a_2732_ = v_val_2773_;
goto v___jp_2731_;
}
v___jp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2735_ = l_Lean_addMacroScope(v_a_2732_, v___x_2734_, v_a_2728_);
v___x_2736_ = lean_box(0);
lean_inc(v___x_2730_);
v___x_2737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2730_);
lean_ctor_set(v___x_2737_, 1, v___x_2733_);
lean_ctor_set(v___x_2737_, 2, v___x_2735_);
lean_ctor_set(v___x_2737_, 3, v___x_2736_);
v___x_2738_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2730_);
v___x_2739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2730_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2730_);
v___x_2741_ = l_Lean_Syntax_node1(v___x_2730_, v___x_2740_, v_stx_1755_);
v___x_2742_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2754_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2754_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2754_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2747_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2730_);
v___x_2748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2730_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_Syntax_node4(v___x_2730_, v___x_1767_, v___x_2737_, v___x_2739_, v___x_2741_, v___x_2748_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v_a_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2750_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v___x_2741_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___x_2737_);
lean_dec(v___x_2730_);
v_a_2755_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2742_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2742_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2774_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2727_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2727_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2782_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2725_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2725_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v_val_2790_; lean_object* v___x_2791_; 
lean_dec(v_id_1754_);
v_val_2790_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2790_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2791_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2790_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2791_);
v_pat_1760_ = v_a_2792_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_stx_1755_);
v_a_2793_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2791_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2791_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = lean_unsigned_to_nat(2u);
v___x_2803_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2802_);
lean_inc(v___x_2803_);
v___x_2804_ = l_Lean_Syntax_matchesNull(v___x_2803_, v___x_2801_);
if (v___x_2804_ == 0)
{
lean_dec(v___x_2803_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v_quotContext_x3f_2809_; lean_object* v___x_2810_; lean_object* v_a_2812_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2807_);
v_quotContext_x3f_2809_ = lean_ctor_get(v_a_1756_, 5);
v___x_2810_ = l_Lean_SourceInfo_fromRef(v_a_2806_, v___x_2804_);
lean_dec(v_a_2806_);
if (lean_obj_tag(v_quotContext_x3f_2809_) == 0)
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref(v___x_2843_);
v_a_2812_ = v_a_2844_;
goto v___jp_2811_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v___x_2810_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2845_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2843_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2843_);
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
lean_object* v_val_2853_; 
v_val_2853_ = lean_ctor_get(v_quotContext_x3f_2809_, 0);
lean_inc(v_val_2853_);
v_a_2812_ = v_val_2853_;
goto v___jp_2811_;
}
v___jp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2813_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2814_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2815_ = l_Lean_addMacroScope(v_a_2812_, v___x_2814_, v_a_2808_);
v___x_2816_ = lean_box(0);
lean_inc(v___x_2810_);
v___x_2817_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2810_);
lean_ctor_set(v___x_2817_, 1, v___x_2813_);
lean_ctor_set(v___x_2817_, 2, v___x_2815_);
lean_ctor_set(v___x_2817_, 3, v___x_2816_);
v___x_2818_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2810_);
v___x_2819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2810_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2810_);
v___x_2821_ = l_Lean_Syntax_node1(v___x_2810_, v___x_2820_, v_stx_1755_);
v___x_2822_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2834_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2834_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2834_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2810_);
v___x_2828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2810_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_Syntax_node4(v___x_2810_, v___x_1767_, v___x_2817_, v___x_2819_, v___x_2821_, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2830_);
v___x_2832_ = v___x_2825_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v___x_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2810_);
v_a_2835_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2822_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2822_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_a_2806_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2854_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2807_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2807_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2862_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2805_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2805_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_val_2870_; lean_object* v___x_2871_; 
lean_dec(v_id_1754_);
v_val_2870_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_2870_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_2871_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_2870_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v_pat_1760_ = v_a_2872_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_stx_1755_);
v_a_2873_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2871_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v_stx_2881_; lean_object* v___x_2882_; 
lean_dec(v_stx_1755_);
v_stx_2881_ = l_Lean_Syntax_getArg(v___x_2803_, v___x_2713_);
lean_dec(v___x_2803_);
lean_inc_ref(v_a_1756_);
v___x_2882_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1753_, v_id_1754_, v_stx_2881_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2945_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v_fst_2884_ = lean_ctor_get(v_a_2883_, 0);
v_snd_2885_ = lean_ctor_get(v_a_2883_, 1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_a_2883_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2887_ = v_a_2883_;
v_isShared_2888_ = v_isSharedCheck_2945_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_snd_2885_);
lean_inc(v_fst_2884_);
lean_dec(v_a_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2945_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2928_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2928_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2928_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_quotContext_x3f_2896_; lean_object* v___x_2897_; lean_object* v_a_2899_; 
v_quotContext_x3f_2896_ = lean_ctor_get(v_a_1756_, 5);
lean_inc(v_quotContext_x3f_2896_);
lean_dec_ref(v_a_1756_);
v___x_2897_ = l_Lean_SourceInfo_fromRef(v_a_2890_, v___x_2722_);
lean_dec(v_a_2890_);
if (lean_obj_tag(v_quotContext_x3f_2896_) == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
v_a_2899_ = v_a_2918_;
goto v___jp_2898_;
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v___x_2897_);
lean_del_object(v___x_2894_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2887_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
v_a_2919_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2917_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2917_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_object* v_val_2927_; 
v_val_2927_ = lean_ctor_get(v_quotContext_x3f_2896_, 0);
lean_inc(v_val_2927_);
lean_dec_ref(v_quotContext_x3f_2896_);
v_a_2899_ = v_val_2927_;
goto v___jp_2898_;
}
v___jp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2900_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_2901_ = l_Lean_addMacroScope(v_a_2899_, v___x_2723_, v_a_2892_);
v___x_2902_ = lean_box(0);
lean_inc(v___x_2897_);
v___x_2903_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2897_);
lean_ctor_set(v___x_2903_, 1, v___x_2900_);
lean_ctor_set(v___x_2903_, 2, v___x_2901_);
lean_ctor_set(v___x_2903_, 3, v___x_2902_);
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2897_);
v___x_2905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2897_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v___x_2897_);
v___x_2907_ = l_Lean_Syntax_node1(v___x_2897_, v___x_2906_, v_fst_2884_);
v___x_2908_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2897_);
v___x_2909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2897_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = l_Lean_Syntax_node4(v___x_2897_, v___x_1767_, v___x_2903_, v___x_2905_, v___x_2907_, v___x_2909_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2910_);
v___x_2912_ = v___x_2887_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_snd_2885_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2912_);
v___x_2914_ = v___x_2894_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_dec_ref(v_a_1756_);
v_a_2929_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2891_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2891_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_del_object(v___x_2887_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_dec_ref(v_a_1756_);
v_a_2937_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2889_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2889_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_1756_);
return v___x_2882_;
}
}
}
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
lean_dec(v___x_2714_);
v___x_2946_ = lean_unsigned_to_nat(1u);
v___x_2947_ = lean_unsigned_to_nat(2u);
v___x_2948_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_2947_);
lean_inc(v___x_2948_);
v___x_2949_ = l_Lean_Syntax_matchesNull(v___x_2948_, v___x_2946_);
if (v___x_2949_ == 0)
{
lean_dec(v___x_2948_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref(v___x_2950_);
v___x_2952_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_quotContext_x3f_2954_; lean_object* v___x_2955_; lean_object* v_a_2957_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2952_);
v_quotContext_x3f_2954_ = lean_ctor_get(v_a_1756_, 5);
v___x_2955_ = l_Lean_SourceInfo_fromRef(v_a_2951_, v___x_2949_);
lean_dec(v_a_2951_);
if (lean_obj_tag(v_quotContext_x3f_2954_) == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___x_2988_);
v_a_2957_ = v_a_2989_;
goto v___jp_2956_;
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v___x_2955_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2990_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2988_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2988_);
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
lean_object* v_val_2998_; 
v_val_2998_ = lean_ctor_get(v_quotContext_x3f_2954_, 0);
lean_inc(v_val_2998_);
v_a_2957_ = v_val_2998_;
goto v___jp_2956_;
}
v___jp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2958_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2959_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2960_ = l_Lean_addMacroScope(v_a_2957_, v___x_2959_, v_a_2953_);
v___x_2961_ = lean_box(0);
lean_inc(v___x_2955_);
v___x_2962_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2955_);
lean_ctor_set(v___x_2962_, 1, v___x_2958_);
lean_ctor_set(v___x_2962_, 2, v___x_2960_);
lean_ctor_set(v___x_2962_, 3, v___x_2961_);
v___x_2963_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_2955_);
v___x_2964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2955_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_2955_);
v___x_2966_ = l_Lean_Syntax_node1(v___x_2955_, v___x_2965_, v_stx_1755_);
v___x_2967_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2979_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2979_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2979_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2955_);
v___x_2973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2955_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_Syntax_node4(v___x_2955_, v___x_1767_, v___x_2962_, v___x_2964_, v___x_2966_, v___x_2973_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v_a_2968_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2975_);
v___x_2977_ = v___x_2970_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v___x_2966_);
lean_dec_ref(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec(v___x_2955_);
v_a_2980_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2967_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2967_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2951_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_2999_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2952_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2952_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3007_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2950_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2950_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_val_3015_; lean_object* v___x_3016_; 
lean_dec(v_id_1754_);
v_val_3015_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3015_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3016_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3015_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref(v___x_3016_);
v_pat_1760_ = v_a_3017_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_stx_1755_);
v_a_3018_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3016_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3016_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3026_ = l_Lean_Syntax_getArg(v___x_2948_, v___x_2713_);
lean_dec(v___x_2948_);
v___x_3027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3026_);
v___x_3028_ = l_Lean_Syntax_isOfKind(v___x_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v___x_3026_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v___x_3031_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v_quotContext_x3f_3033_; lean_object* v___x_3034_; lean_object* v_a_3036_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v_quotContext_x3f_3033_ = lean_ctor_get(v_a_1756_, 5);
v___x_3034_ = l_Lean_SourceInfo_fromRef(v_a_3030_, v___x_3028_);
lean_dec(v_a_3030_);
if (lean_obj_tag(v_quotContext_x3f_3033_) == 0)
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v_a_3036_ = v_a_3068_;
goto v___jp_3035_;
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v___x_3034_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3069_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3067_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3067_);
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
lean_object* v_val_3077_; 
v_val_3077_ = lean_ctor_get(v_quotContext_x3f_3033_, 0);
lean_inc(v_val_3077_);
v_a_3036_ = v_val_3077_;
goto v___jp_3035_;
}
v___jp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3037_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3038_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3039_ = l_Lean_addMacroScope(v_a_3036_, v___x_3038_, v_a_3032_);
v___x_3040_ = lean_box(0);
lean_inc(v___x_3034_);
v___x_3041_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3034_);
lean_ctor_set(v___x_3041_, 1, v___x_3037_);
lean_ctor_set(v___x_3041_, 2, v___x_3039_);
lean_ctor_set(v___x_3041_, 3, v___x_3040_);
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3034_);
v___x_3043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3034_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3034_);
v___x_3045_ = l_Lean_Syntax_node1(v___x_3034_, v___x_3044_, v_stx_1755_);
v___x_3046_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3058_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3058_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3058_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3051_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3034_);
v___x_3052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3034_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = l_Lean_Syntax_node4(v___x_3034_, v___x_1767_, v___x_3041_, v___x_3043_, v___x_3045_, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
lean_ctor_set(v___x_3054_, 1, v_a_3047_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3054_);
v___x_3056_ = v___x_3049_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec(v___x_3045_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v___x_3041_);
lean_dec(v___x_3034_);
v_a_3059_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3046_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3046_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_3030_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3078_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3031_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3031_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
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
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3086_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3029_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3029_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_val_3094_; lean_object* v___x_3095_; 
lean_dec(v_id_1754_);
v_val_3094_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3094_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3095_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3094_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref(v___x_3095_);
v_pat_1760_ = v_a_3096_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_stx_1755_);
v_a_3097_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3095_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3095_);
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
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3105_ = l_Lean_Syntax_getArg(v___x_3026_, v___x_2713_);
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3107_ = l_Lean_Syntax_matchesIdent(v___x_3105_, v___x_3106_);
lean_dec(v___x_3105_);
if (v___x_3107_ == 0)
{
lean_dec(v___x_3026_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref(v___x_3108_);
v___x_3110_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v_quotContext_x3f_3112_; lean_object* v___x_3113_; lean_object* v_a_3115_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___x_3110_);
v_quotContext_x3f_3112_ = lean_ctor_get(v_a_1756_, 5);
v___x_3113_ = l_Lean_SourceInfo_fromRef(v_a_3109_, v___x_3107_);
lean_dec(v_a_3109_);
if (lean_obj_tag(v_quotContext_x3f_3112_) == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref(v___x_3146_);
v_a_3115_ = v_a_3147_;
goto v___jp_3114_;
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v___x_3113_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3148_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3146_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3146_);
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
lean_object* v_val_3156_; 
v_val_3156_ = lean_ctor_get(v_quotContext_x3f_3112_, 0);
lean_inc(v_val_3156_);
v_a_3115_ = v_val_3156_;
goto v___jp_3114_;
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3116_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3117_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3118_ = l_Lean_addMacroScope(v_a_3115_, v___x_3117_, v_a_3111_);
v___x_3119_ = lean_box(0);
lean_inc(v___x_3113_);
v___x_3120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3113_);
lean_ctor_set(v___x_3120_, 1, v___x_3116_);
lean_ctor_set(v___x_3120_, 2, v___x_3118_);
lean_ctor_set(v___x_3120_, 3, v___x_3119_);
v___x_3121_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3113_);
v___x_3122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3113_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3113_);
v___x_3124_ = l_Lean_Syntax_node1(v___x_3113_, v___x_3123_, v_stx_1755_);
v___x_3125_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3137_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3137_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3137_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3130_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3113_);
v___x_3131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3113_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = l_Lean_Syntax_node4(v___x_3113_, v___x_1767_, v___x_3120_, v___x_3122_, v___x_3124_, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v_a_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3133_);
v___x_3135_ = v___x_3128_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v___x_3124_);
lean_dec_ref(v___x_3122_);
lean_dec_ref(v___x_3120_);
lean_dec(v___x_3113_);
v_a_3138_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3125_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3125_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec(v_a_3109_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3157_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3110_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3110_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
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
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3165_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3108_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3108_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_val_3173_; lean_object* v___x_3174_; 
lean_dec(v_id_1754_);
v_val_3173_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3173_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3174_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3173_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v_pat_1760_ = v_a_3175_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_stx_1755_);
v_a_3176_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3174_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3174_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
else
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = l_Lean_Syntax_getArg(v___x_3026_, v___x_2946_);
lean_dec(v___x_3026_);
v___x_3185_ = l_Lean_Syntax_matchesNull(v___x_3184_, v___x_2713_);
if (v___x_3185_ == 0)
{
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3188_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref(v___x_3186_);
v___x_3188_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v_quotContext_x3f_3190_; lean_object* v___x_3191_; lean_object* v_a_3193_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___x_3188_);
v_quotContext_x3f_3190_ = lean_ctor_get(v_a_1756_, 5);
v___x_3191_ = l_Lean_SourceInfo_fromRef(v_a_3187_, v___x_3185_);
lean_dec(v_a_3187_);
if (lean_obj_tag(v_quotContext_x3f_3190_) == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref(v___x_3224_);
v_a_3193_ = v_a_3225_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec(v___x_3191_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3226_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3224_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3224_);
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
lean_object* v_val_3234_; 
v_val_3234_ = lean_ctor_get(v_quotContext_x3f_3190_, 0);
lean_inc(v_val_3234_);
v_a_3193_ = v_val_3234_;
goto v___jp_3192_;
}
v___jp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3194_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3195_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3196_ = l_Lean_addMacroScope(v_a_3193_, v___x_3195_, v_a_3189_);
v___x_3197_ = lean_box(0);
lean_inc(v___x_3191_);
v___x_3198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3191_);
lean_ctor_set(v___x_3198_, 1, v___x_3194_);
lean_ctor_set(v___x_3198_, 2, v___x_3196_);
lean_ctor_set(v___x_3198_, 3, v___x_3197_);
v___x_3199_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3191_);
v___x_3200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3191_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3191_);
v___x_3202_ = l_Lean_Syntax_node1(v___x_3191_, v___x_3201_, v_stx_1755_);
v___x_3203_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3215_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3215_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3215_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3208_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3191_);
v___x_3209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3191_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l_Lean_Syntax_node4(v___x_3191_, v___x_1767_, v___x_3198_, v___x_3200_, v___x_3202_, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v_a_3204_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3211_);
v___x_3213_ = v___x_3206_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v___x_3202_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v___x_3198_);
lean_dec(v___x_3191_);
v_a_3216_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3203_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3203_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_a_3187_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3235_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3188_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3188_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3243_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3186_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3186_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v_val_3251_; lean_object* v___x_3252_; 
lean_dec(v_id_1754_);
v_val_3251_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3251_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3252_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3251_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v_pat_1760_ = v_a_3253_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_stx_1755_);
v_a_3254_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3252_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3252_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_id_x3f_1753_);
v___x_3262_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3263_ = lean_box(0);
v___x_3264_ = l_Lean_Syntax_mkAntiquotNode(v___x_3262_, v_id_1754_, v___x_2713_, v___x_3263_, v___x_2720_);
v_pat_1760_ = v___x_3264_;
goto v___jp_1759_;
}
}
}
}
}
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
lean_dec(v___x_2714_);
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = lean_unsigned_to_nat(2u);
v___x_3267_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_3266_);
lean_inc(v___x_3267_);
v___x_3268_ = l_Lean_Syntax_matchesNull(v___x_3267_, v___x_3265_);
if (v___x_3268_ == 0)
{
lean_dec(v___x_3267_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v_quotContext_x3f_3273_; lean_object* v___x_3274_; lean_object* v_a_3276_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v_quotContext_x3f_3273_ = lean_ctor_get(v_a_1756_, 5);
v___x_3274_ = l_Lean_SourceInfo_fromRef(v_a_3270_, v___x_3268_);
lean_dec(v_a_3270_);
if (lean_obj_tag(v_quotContext_x3f_3273_) == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___x_3307_);
v_a_3276_ = v_a_3308_;
goto v___jp_3275_;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v___x_3274_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3309_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3307_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3307_);
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
lean_object* v_val_3317_; 
v_val_3317_ = lean_ctor_get(v_quotContext_x3f_3273_, 0);
lean_inc(v_val_3317_);
v_a_3276_ = v_val_3317_;
goto v___jp_3275_;
}
v___jp_3275_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3277_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3279_ = l_Lean_addMacroScope(v_a_3276_, v___x_3278_, v_a_3272_);
v___x_3280_ = lean_box(0);
lean_inc(v___x_3274_);
v___x_3281_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3274_);
lean_ctor_set(v___x_3281_, 1, v___x_3277_);
lean_ctor_set(v___x_3281_, 2, v___x_3279_);
lean_ctor_set(v___x_3281_, 3, v___x_3280_);
v___x_3282_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3274_);
v___x_3283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3274_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3274_);
v___x_3285_ = l_Lean_Syntax_node1(v___x_3274_, v___x_3284_, v_stx_1755_);
v___x_3286_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3298_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3298_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3298_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3274_);
v___x_3292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3274_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = l_Lean_Syntax_node4(v___x_3274_, v___x_1767_, v___x_3281_, v___x_3283_, v___x_3285_, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_a_3287_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3294_);
v___x_3296_ = v___x_3289_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v___x_3285_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v___x_3281_);
lean_dec(v___x_3274_);
v_a_3299_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3286_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3286_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_a_3270_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3318_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3271_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3271_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3326_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3269_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3269_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v_val_3334_; lean_object* v___x_3335_; 
lean_dec(v_id_1754_);
v_val_3334_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3334_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3335_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3334_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v_pat_1760_ = v_a_3336_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_stx_1755_);
v_a_3337_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3335_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3335_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
else
{
lean_object* v_stx_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec(v_id_x3f_1753_);
v_stx_3345_ = l_Lean_Syntax_getArg(v___x_3267_, v___x_2713_);
lean_dec(v___x_3267_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3347_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2717_, v_stx_3345_, v_id_1754_, v___x_3346_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref(v___x_3347_);
v_pat_1760_ = v_a_3348_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_stx_1755_);
v_a_3349_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3347_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3347_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
lean_dec(v___x_2714_);
v___x_3357_ = lean_unsigned_to_nat(1u);
v___x_3358_ = lean_unsigned_to_nat(2u);
v___x_3359_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_3358_);
lean_inc(v___x_3359_);
v___x_3360_ = l_Lean_Syntax_matchesNull(v___x_3359_, v___x_3357_);
if (v___x_3360_ == 0)
{
lean_dec(v___x_3359_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v_quotContext_x3f_3365_; lean_object* v___x_3366_; lean_object* v_a_3368_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref(v___x_3363_);
v_quotContext_x3f_3365_ = lean_ctor_get(v_a_1756_, 5);
v___x_3366_ = l_Lean_SourceInfo_fromRef(v_a_3362_, v___x_3360_);
lean_dec(v_a_3362_);
if (lean_obj_tag(v_quotContext_x3f_3365_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
v_a_3368_ = v_a_3400_;
goto v___jp_3367_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v___x_3366_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3401_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3399_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3399_);
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
lean_object* v_val_3409_; 
v_val_3409_ = lean_ctor_get(v_quotContext_x3f_3365_, 0);
lean_inc(v_val_3409_);
v_a_3368_ = v_val_3409_;
goto v___jp_3367_;
}
v___jp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3369_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3371_ = l_Lean_addMacroScope(v_a_3368_, v___x_3370_, v_a_3364_);
v___x_3372_ = lean_box(0);
lean_inc(v___x_3366_);
v___x_3373_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3366_);
lean_ctor_set(v___x_3373_, 1, v___x_3369_);
lean_ctor_set(v___x_3373_, 2, v___x_3371_);
lean_ctor_set(v___x_3373_, 3, v___x_3372_);
v___x_3374_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3366_);
v___x_3375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3366_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3366_);
v___x_3377_ = l_Lean_Syntax_node1(v___x_3366_, v___x_3376_, v_stx_1755_);
v___x_3378_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3390_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3390_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3390_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3383_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3366_);
v___x_3384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3366_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_Syntax_node4(v___x_3366_, v___x_1767_, v___x_3373_, v___x_3375_, v___x_3377_, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v_a_3379_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3386_);
v___x_3388_ = v___x_3381_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v___x_3377_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3373_);
lean_dec(v___x_3366_);
v_a_3391_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3378_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3378_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_a_3362_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3410_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3363_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3363_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3418_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3361_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3361_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_val_3426_; lean_object* v___x_3427_; 
lean_dec(v_id_1754_);
v_val_3426_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3426_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3427_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3426_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v_pat_1760_ = v_a_3428_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v_stx_1755_);
v_a_3429_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3427_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3427_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
else
{
lean_object* v_stx_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec(v_id_x3f_1753_);
v_stx_3437_ = l_Lean_Syntax_getArg(v___x_3359_, v___x_2713_);
lean_dec(v___x_3359_);
v___x_3438_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3439_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2717_, v_stx_3437_, v_id_1754_, v___x_3438_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref(v___x_3439_);
v_pat_1760_ = v_a_3440_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec(v_stx_1755_);
v_a_3441_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3439_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3439_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
lean_dec(v___x_2714_);
v___x_3449_ = lean_unsigned_to_nat(1u);
v___x_3450_ = lean_unsigned_to_nat(2u);
v___x_3451_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_3450_);
lean_inc(v___x_3451_);
v___x_3452_ = l_Lean_Syntax_matchesNull(v___x_3451_, v___x_3449_);
if (v___x_3452_ == 0)
{
lean_dec(v___x_3451_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v_quotContext_x3f_3457_; lean_object* v___x_3458_; lean_object* v_a_3460_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref(v___x_3455_);
v_quotContext_x3f_3457_ = lean_ctor_get(v_a_1756_, 5);
v___x_3458_ = l_Lean_SourceInfo_fromRef(v_a_3454_, v___x_3452_);
lean_dec(v_a_3454_);
if (lean_obj_tag(v_quotContext_x3f_3457_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
v_a_3460_ = v_a_3492_;
goto v___jp_3459_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3493_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3491_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3491_);
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
lean_object* v_val_3501_; 
v_val_3501_ = lean_ctor_get(v_quotContext_x3f_3457_, 0);
lean_inc(v_val_3501_);
v_a_3460_ = v_val_3501_;
goto v___jp_3459_;
}
v___jp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3461_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3462_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3463_ = l_Lean_addMacroScope(v_a_3460_, v___x_3462_, v_a_3456_);
v___x_3464_ = lean_box(0);
lean_inc(v___x_3458_);
v___x_3465_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3458_);
lean_ctor_set(v___x_3465_, 1, v___x_3461_);
lean_ctor_set(v___x_3465_, 2, v___x_3463_);
lean_ctor_set(v___x_3465_, 3, v___x_3464_);
v___x_3466_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3458_);
v___x_3467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3458_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3458_);
v___x_3469_ = l_Lean_Syntax_node1(v___x_3458_, v___x_3468_, v_stx_1755_);
v___x_3470_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3482_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3482_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3482_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3475_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3458_);
v___x_3476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3458_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_Syntax_node4(v___x_3458_, v___x_1767_, v___x_3465_, v___x_3467_, v___x_3469_, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v_a_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3478_);
v___x_3480_ = v___x_3473_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v___x_3469_);
lean_dec_ref(v___x_3467_);
lean_dec_ref(v___x_3465_);
lean_dec(v___x_3458_);
v_a_3483_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3470_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3470_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_a_3454_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3502_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3455_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3455_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3510_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3453_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3453_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_val_3518_; lean_object* v___x_3519_; 
lean_dec(v_id_1754_);
v_val_3518_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3518_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3519_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3518_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v_pat_1760_ = v_a_3520_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_stx_1755_);
v_a_3521_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3519_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3519_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
else
{
lean_object* v_stx_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec(v_id_x3f_1753_);
v_stx_3529_ = l_Lean_Syntax_getArg(v___x_3451_, v___x_2713_);
lean_dec(v___x_3451_);
v___x_3530_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3531_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2715_, v_stx_3529_, v_id_1754_, v___x_3530_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref(v___x_3531_);
v_pat_1760_ = v_a_3532_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_stx_1755_);
v_a_3533_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3531_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
v___jp_1768_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1774_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1775_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1776_ = l_Lean_addMacroScope(v_a_1773_, v___x_1775_, v___y_1770_);
v___x_1777_ = lean_box(0);
lean_inc(v___y_1771_);
v___x_1778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1771_);
lean_ctor_set(v___x_1778_, 1, v___x_1774_);
lean_ctor_set(v___x_1778_, 2, v___x_1776_);
lean_ctor_set(v___x_1778_, 3, v___x_1777_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___y_1771_);
v___x_1780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___y_1771_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___y_1771_);
v___x_1782_ = l_Lean_Syntax_node1(v___y_1771_, v___x_1781_, v_stx_1755_);
v___x_1783_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v___y_1772_, v___y_1769_);
lean_dec_ref(v___y_1772_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1795_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1771_);
v___x_1789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___y_1771_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_Syntax_node4(v___y_1771_, v___x_1767_, v___x_1778_, v___x_1780_, v___x_1782_, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v_a_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1791_);
v___x_1793_ = v___x_1786_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v___x_1782_);
lean_dec_ref(v___x_1780_);
lean_dec_ref(v___x_1778_);
lean_dec(v___y_1771_);
v_a_1796_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1783_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1783_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
v___jp_1804_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1810_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1812_ = l_Lean_addMacroScope(v_a_1809_, v___x_1811_, v___y_1805_);
v___x_1813_ = lean_box(0);
lean_inc(v___y_1806_);
v___x_1814_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1814_, 0, v___y_1806_);
lean_ctor_set(v___x_1814_, 1, v___x_1810_);
lean_ctor_set(v___x_1814_, 2, v___x_1812_);
lean_ctor_set(v___x_1814_, 3, v___x_1813_);
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___y_1806_);
v___x_1816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1806_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___y_1806_);
v___x_1818_ = l_Lean_Syntax_node1(v___y_1806_, v___x_1817_, v_stx_1755_);
v___x_1819_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v___y_1807_, v___y_1808_);
lean_dec_ref(v___y_1807_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1831_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1824_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1806_);
v___x_1825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___y_1806_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_Syntax_node4(v___y_1806_, v___x_1767_, v___x_1814_, v___x_1816_, v___x_1818_, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_a_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1827_);
v___x_1829_ = v___x_1822_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v___x_1818_);
lean_dec_ref(v___x_1816_);
lean_dec_ref(v___x_1814_);
lean_dec(v___y_1806_);
v_a_1832_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1819_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1819_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_3541_);
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3542_);
v___x_3544_ = l_Lean_Syntax_isOfKind(v___x_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_dec(v___x_3542_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v_quotContext_x3f_3549_; lean_object* v___x_3550_; lean_object* v_a_3552_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
v_quotContext_x3f_3549_ = lean_ctor_get(v_a_1756_, 5);
v___x_3550_ = l_Lean_SourceInfo_fromRef(v_a_3546_, v___x_3544_);
lean_dec(v_a_3546_);
if (lean_obj_tag(v_quotContext_x3f_3549_) == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref(v___x_3584_);
v_a_3552_ = v_a_3585_;
goto v___jp_3551_;
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v___x_3550_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3586_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3584_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3584_);
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
lean_object* v_val_3594_; 
v_val_3594_ = lean_ctor_get(v_quotContext_x3f_3549_, 0);
lean_inc(v_val_3594_);
v_a_3552_ = v_val_3594_;
goto v___jp_3551_;
}
v___jp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3553_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3554_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3555_ = l_Lean_addMacroScope(v_a_3552_, v___x_3554_, v_a_3548_);
v___x_3556_ = lean_box(0);
lean_inc(v___x_3550_);
v___x_3557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3550_);
lean_ctor_set(v___x_3557_, 1, v___x_3553_);
lean_ctor_set(v___x_3557_, 2, v___x_3555_);
lean_ctor_set(v___x_3557_, 3, v___x_3556_);
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3550_);
v___x_3559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3550_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3550_);
v___x_3561_ = l_Lean_Syntax_node1(v___x_3550_, v___x_3560_, v_stx_1755_);
v___x_3562_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3575_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3575_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3575_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3550_);
v___x_3568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3550_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3570_ = l_Lean_Syntax_node4(v___x_3550_, v___x_3569_, v___x_3557_, v___x_3559_, v___x_3561_, v___x_3568_);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v_a_3563_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3571_);
v___x_3573_ = v___x_3565_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v___x_3561_);
lean_dec_ref(v___x_3559_);
lean_dec_ref(v___x_3557_);
lean_dec(v___x_3550_);
v_a_3576_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3562_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3562_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_a_3546_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3595_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3547_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3547_);
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
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3603_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3545_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3545_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3612_; 
lean_dec(v_id_1754_);
v_val_3611_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3611_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3612_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3611_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
v_pat_1760_ = v_a_3613_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_stx_1755_);
v_a_3614_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3612_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3612_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_dec(v_id_x3f_1753_);
v___x_3622_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3622_, 0, v___x_3542_);
v___x_3623_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3622_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v___x_3623_);
v___x_3625_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3626_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3627_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3628_ = lean_unsigned_to_nat(4u);
v___x_3629_ = lean_mk_empty_array_with_capacity(v___x_3628_);
v___x_3630_ = lean_array_push(v___x_3629_, v_a_3624_);
v___x_3631_ = lean_array_push(v___x_3630_, v___x_3626_);
v___x_3632_ = lean_array_push(v___x_3631_, v___x_3627_);
v___x_3633_ = lean_array_push(v___x_3632_, v_id_1754_);
v___x_3634_ = lean_box(2);
v___x_3635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___x_3625_);
lean_ctor_set(v___x_3635_, 2, v___x_3633_);
v_pat_1760_ = v___x_3635_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3636_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3623_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3623_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3644_ = lean_unsigned_to_nat(0u);
v___x_3645_ = l_Lean_Syntax_getArg(v_stx_1755_, v___x_3644_);
v___x_3646_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3645_);
v___x_3647_ = l_Lean_Syntax_isOfKind(v___x_3645_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_dec(v___x_3645_);
if (lean_obj_tag(v_id_x3f_1753_) == 0)
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_Elab_Command_getRef___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1756_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v_quotContext_x3f_3652_; lean_object* v___x_3653_; lean_object* v_a_3655_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v_quotContext_x3f_3652_ = lean_ctor_get(v_a_1756_, 5);
v___x_3653_ = l_Lean_SourceInfo_fromRef(v_a_3649_, v___x_3647_);
lean_dec(v_a_3649_);
if (lean_obj_tag(v_quotContext_x3f_3652_) == 0)
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1757_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v___x_3687_);
v_a_3655_ = v_a_3688_;
goto v___jp_3654_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v___x_3653_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3689_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3687_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3687_);
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
lean_object* v_val_3697_; 
v_val_3697_ = lean_ctor_get(v_quotContext_x3f_3652_, 0);
lean_inc(v_val_3697_);
v_a_3655_ = v_val_3697_;
goto v___jp_3654_;
}
v___jp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3656_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3657_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3658_ = l_Lean_addMacroScope(v_a_3655_, v___x_3657_, v_a_3651_);
v___x_3659_ = lean_box(0);
lean_inc(v___x_3653_);
v___x_3660_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3653_);
lean_ctor_set(v___x_3660_, 1, v___x_3656_);
lean_ctor_set(v___x_3660_, 2, v___x_3658_);
lean_ctor_set(v___x_3660_, 3, v___x_3659_);
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
lean_inc(v___x_3653_);
v___x_3662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3653_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1755_);
lean_inc(v___x_3653_);
v___x_3664_ = l_Lean_Syntax_node1(v___x_3653_, v___x_3663_, v_stx_1755_);
v___x_3665_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_id_1754_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3678_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3678_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3678_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3653_);
v___x_3671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3653_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3673_ = l_Lean_Syntax_node4(v___x_3653_, v___x_3672_, v___x_3660_, v___x_3662_, v___x_3664_, v___x_3671_);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v_a_3666_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3674_);
v___x_3676_ = v___x_3668_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v___x_3664_);
lean_dec_ref(v___x_3662_);
lean_dec_ref(v___x_3660_);
lean_dec(v___x_3653_);
v_a_3679_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3665_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3665_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v_a_3649_);
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3698_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3650_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3650_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_a_1756_);
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3706_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3648_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3648_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
else
{
lean_object* v_val_3714_; lean_object* v___x_3715_; 
lean_dec(v_id_1754_);
v_val_3714_ = lean_ctor_get(v_id_x3f_1753_, 0);
lean_inc(v_val_3714_);
lean_dec_ref(v_id_x3f_1753_);
lean_inc(v_stx_1755_);
v___x_3715_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1755_, v_val_3714_, v_a_1756_, v_a_1757_);
lean_dec_ref(v_a_1756_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref(v___x_3715_);
v_pat_1760_ = v_a_3716_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v_stx_1755_);
v_a_3717_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3715_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3715_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec(v_id_x3f_1753_);
v___x_3725_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3725_, 0, v___x_3645_);
v___x_3726_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3725_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref(v___x_3726_);
v___x_3728_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3729_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3730_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3731_ = lean_unsigned_to_nat(4u);
v___x_3732_ = lean_mk_empty_array_with_capacity(v___x_3731_);
v___x_3733_ = lean_array_push(v___x_3732_, v_a_3727_);
v___x_3734_ = lean_array_push(v___x_3733_, v___x_3729_);
v___x_3735_ = lean_array_push(v___x_3734_, v___x_3730_);
v___x_3736_ = lean_array_push(v___x_3735_, v_id_1754_);
v___x_3737_ = lean_box(2);
v___x_3738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v___x_3728_);
lean_ctor_set(v___x_3738_, 2, v___x_3736_);
v_pat_1760_ = v___x_3738_;
goto v___jp_1759_;
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_stx_1755_);
lean_dec(v_id_1754_);
v_a_3739_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3726_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3726_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
v___jp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_stx_1755_);
lean_ctor_set(v___x_1761_, 1, v_pat_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3747_, lean_object* v_id_3748_, lean_object* v_stx_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3747_, v_id_3748_, v_stx_3749_, v_a_3750_, v_a_3751_);
lean_dec(v_a_3751_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___redArg(v_cls_3754_, v___y_3756_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_00_u03b1_3764_, lean_object* v_x_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___redArg(v_x_3765_, v___y_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3769_, lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_00_u03b1_3769_, v_x_3770_, v___y_3771_, v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec_ref(v_x_3770_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3774_, lean_object* v_ref_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(v_ref_3775_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3780_, lean_object* v_ref_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3780_, v_ref_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10(lean_object* v_00_u03b1_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___boxed(lean_object* v_00_u03b1_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10(v_00_u03b1_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3796_, lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
lean_inc_ref(v___y_3798_);
v___x_3801_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3797_, v___y_3798_, v___y_3799_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3802_, lean_object* v_x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3802_, v_x_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_3808_, lean_object* v_as_x27_3809_, lean_object* v_b_3810_, lean_object* v_a_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___redArg(v_as_x27_3809_, v_b_3810_, v___y_3812_, v___y_3813_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_3816_, lean_object* v_as_x27_3817_, lean_object* v_b_3818_, lean_object* v_a_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_3816_, v_as_x27_3817_, v_b_3818_, v_a_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v_as_3816_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3824_, lean_object* v_ref_3825_, lean_object* v_msg_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3825_, v_msg_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_ref_3832_, lean_object* v_msg_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3831_, v_ref_3832_, v_msg_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v_ref_3832_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3838_, lean_object* v_m_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___redArg(v_m_3839_, v_a_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3842_, lean_object* v_m_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8(v_00_u03b2_3842_, v_m_3843_, v_a_3844_);
lean_dec(v_a_3844_);
lean_dec_ref(v_m_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_3846_, lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___redArg(v_x_3847_, v_x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3850_, lean_object* v_x_3851_, lean_object* v_x_3852_){
_start:
{
uint8_t v_res_3853_; lean_object* v_r_3854_; 
v_res_3853_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9(v_00_u03b2_3850_, v_x_3851_, v_x_3852_);
lean_dec_ref(v_x_3852_);
v_r_3854_ = lean_box(v_res_3853_);
return v_r_3854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3855_, lean_object* v_a_3856_, lean_object* v_x_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___redArg(v_a_3856_, v_x_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3859_, lean_object* v_a_3860_, lean_object* v_x_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__8_spec__12(v_00_u03b2_3859_, v_a_3860_, v_x_3861_);
lean_dec(v_x_3861_);
lean_dec(v_a_3860_);
return v_res_3862_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13(lean_object* v_00_u03b2_3863_, lean_object* v_x_3864_, size_t v_x_3865_, lean_object* v_x_3866_){
_start:
{
uint8_t v___x_3867_; 
v___x_3867_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___redArg(v_x_3864_, v_x_3865_, v_x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3868_, lean_object* v_x_3869_, lean_object* v_x_3870_, lean_object* v_x_3871_){
_start:
{
size_t v_x_90025__boxed_3872_; uint8_t v_res_3873_; lean_object* v_r_3874_; 
v_x_90025__boxed_3872_ = lean_unbox_usize(v_x_3870_);
lean_dec(v_x_3870_);
v_res_3873_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13(v_00_u03b2_3868_, v_x_3869_, v_x_90025__boxed_3872_, v_x_3871_);
lean_dec_ref(v_x_3871_);
v_r_3874_ = lean_box(v_res_3873_);
return v_r_3874_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_3875_, lean_object* v_keys_3876_, lean_object* v_vals_3877_, lean_object* v_heq_3878_, lean_object* v_i_3879_, lean_object* v_k_3880_){
_start:
{
uint8_t v___x_3881_; 
v___x_3881_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_3876_, v_i_3879_, v_k_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_3882_, lean_object* v_keys_3883_, lean_object* v_vals_3884_, lean_object* v_heq_3885_, lean_object* v_i_3886_, lean_object* v_k_3887_){
_start:
{
uint8_t v_res_3888_; lean_object* v_r_3889_; 
v_res_3888_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_spec__6_spec__9_spec__13_spec__16(v_00_u03b2_3882_, v_keys_3883_, v_vals_3884_, v_heq_3885_, v_i_3886_, v_k_3887_);
lean_dec_ref(v_k_3887_);
lean_dec_ref(v_vals_3884_);
lean_dec_ref(v_keys_3883_);
v_r_3889_ = lean_box(v_res_3888_);
return v_r_3889_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_k_3896_){
_start:
{
lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3897_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_3898_ = lean_name_eq(v_k_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
uint8_t v___x_3899_; 
v___x_3899_ = 1;
return v___x_3899_;
}
else
{
uint8_t v___x_3900_; 
v___x_3900_ = 0;
return v___x_3900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_k_3901_){
_start:
{
uint8_t v_res_3902_; lean_object* v_r_3903_; 
v_res_3902_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_3901_);
lean_dec(v_k_3901_);
v_r_3903_ = lean_box(v_res_3902_);
return v_r_3903_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_3914_ = l_String_toRawSubstring_x27(v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v___f_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___f_3921_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_3922_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_3922_, 0, v_stx_3917_);
lean_closure_set(v___x_3922_, 1, v___f_3921_);
lean_inc_ref(v_a_3918_);
v___x_3923_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3922_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref(v___x_3923_);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
lean_inc(v_a_3924_);
v___x_3926_ = l_Lean_Syntax_isOfKind(v_a_3924_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3918_);
v___x_3927_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3936_ = lean_unsigned_to_nat(0u);
v___x_3937_ = l_Lean_Syntax_getArg(v_a_3924_, v___x_3936_);
v___x_3938_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3937_);
v___x_3939_ = l_Lean_Syntax_matchesNull(v___x_3937_, v___x_3938_);
if (v___x_3939_ == 0)
{
uint8_t v___x_3940_; 
v___x_3940_ = l_Lean_Syntax_matchesNull(v___x_3937_, v___x_3936_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3918_);
v___x_3941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
else
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Elab_Command_getRef___redArg(v_a_3918_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3952_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref(v___x_3950_);
v___x_3952_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3918_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v_quotContext_x3f_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v_a_3959_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref(v___x_3952_);
v_quotContext_x3f_3954_ = lean_ctor_get(v_a_3918_, 5);
v___x_3955_ = lean_unsigned_to_nat(1u);
v___x_3956_ = l_Lean_Syntax_getArg(v_a_3924_, v___x_3955_);
lean_dec(v_a_3924_);
v___x_3957_ = l_Lean_SourceInfo_fromRef(v_a_3951_, v___x_3939_);
lean_dec(v_a_3951_);
if (lean_obj_tag(v_quotContext_x3f_3954_) == 0)
{
lean_object* v___x_3967_; lean_object* v_a_3968_; 
v___x_3967_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_3919_);
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref(v___x_3967_);
v_a_3959_ = v_a_3968_;
goto v___jp_3958_;
}
else
{
lean_object* v_val_3969_; 
v_val_3969_ = lean_ctor_get(v_quotContext_x3f_3954_, 0);
lean_inc(v_val_3969_);
v_a_3959_ = v_val_3969_;
goto v___jp_3958_;
}
v___jp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3960_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_3962_ = l_Lean_addMacroScope(v_a_3959_, v___x_3961_, v_a_3953_);
v___x_3963_ = lean_box(0);
v___x_3964_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3957_);
lean_ctor_set(v___x_3964_, 1, v___x_3960_);
lean_ctor_set(v___x_3964_, 2, v___x_3962_);
lean_ctor_set(v___x_3964_, 3, v___x_3963_);
v___x_3965_ = lean_box(0);
v___x_3966_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3965_, v___x_3964_, v___x_3956_, v_a_3918_, v_a_3919_);
return v___x_3966_;
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec(v_a_3951_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3918_);
v_a_3970_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3952_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3952_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3918_);
v_a_3978_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3950_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3950_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3986_ = l_Lean_Syntax_getArg(v___x_3937_, v___x_3936_);
lean_dec(v___x_3937_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_3986_);
v___x_3988_ = l_Lean_Syntax_isOfKind(v___x_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v___x_3986_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3918_);
v___x_3989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__10___redArg();
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3989_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = l_Lean_Syntax_getArg(v_a_3924_, v___x_3998_);
lean_dec(v_a_3924_);
lean_inc(v___x_3986_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3986_);
v___x_4001_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4000_, v___x_3986_, v___x_3999_, v_a_3918_, v_a_3919_);
return v___x_4001_;
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_a_3918_);
v_a_4002_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3923_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3923_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_Elab_Command_expandMacroArg(v_stx_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
return v_res_4014_;
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
