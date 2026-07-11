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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(lean_object* v_id_18_, lean_object* v___x_19_, lean_object* v_x_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = l_Lean_TSyntax_getId(v_id_18_);
v___x_25_ = l_Lean_Parser_getParserAliasInfo(v___x_24_);
lean_dec(v___x_24_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_38_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_38_ == 0)
{
v___x_28_ = v___x_25_;
v_isShared_29_ = v_isSharedCheck_38_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_25_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_38_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v_stackSz_x3f_30_; lean_object* v___x_31_; uint8_t v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v_stackSz_x3f_30_ = lean_ctor_get(v_a_26_, 1);
lean_inc(v_stackSz_x3f_30_);
lean_dec(v_a_26_);
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_19_);
v___x_32_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_30_, v___x_31_);
lean_dec_ref_known(v___x_31_, 1);
lean_dec(v_stackSz_x3f_30_);
v___x_33_ = lean_bool_not(v___x_32_);
v___x_34_ = lean_box(v___x_33_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_34_);
v___x_36_ = v___x_28_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_51_; 
lean_dec(v___x_19_);
v_a_39_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_51_ == 0)
{
v___x_41_ = v___x_25_;
v_isShared_42_ = v_isSharedCheck_51_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_25_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_51_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_ref_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v_ref_43_ = lean_ctor_get(v___y_21_, 7);
v___x_44_ = lean_io_error_to_string(v_a_39_);
v___x_45_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
v___x_46_ = l_Lean_MessageData_ofFormat(v___x_45_);
lean_inc(v_ref_43_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_ref_43_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_47_);
v___x_49_ = v___x_41_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0___boxed(lean_object* v_id_52_, lean_object* v___x_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_52_, v___x_53_, v_x_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v_id_52_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(lean_object* v_as_81_, size_t v_i_82_, size_t v_stop_83_, lean_object* v_b_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_a_89_; uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_eq(v_i_82_, v_stop_83_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v_a_101_; lean_object* v___y_103_; uint8_t v___x_114_; 
v___x_94_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_array_uget_borrowed(v_as_81_, v_i_82_);
lean_inc(v___x_97_);
v___x_114_ = l_Lean_Syntax_isOfKind(v___x_97_, v___x_94_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_97_);
v___x_116_ = l_Lean_Syntax_isOfKind(v___x_97_, v___x_115_);
if (v___x_116_ == 0)
{
goto v___jp_98_;
}
else
{
lean_object* v_id_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_id_117_ = l_Lean_Syntax_getArg(v___x_97_, v___x_95_);
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_117_);
v___x_119_ = l_Lean_Syntax_isOfKind(v_id_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec(v_id_117_);
goto v___jp_98_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = l_Lean_Syntax_getArg(v___x_97_, v___x_120_);
v___x_122_ = l_Lean_Syntax_matchesNull(v___x_121_, v___x_96_);
if (v___x_122_ == 0)
{
lean_dec(v_id_117_);
goto v___jp_98_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = l_Lean_TSyntax_getId(v_id_117_);
lean_dec(v_id_117_);
v___x_124_ = l_Lean_Parser_getParserAliasInfo(v___x_123_);
lean_dec(v___x_123_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v_stackSz_x3f_126_; lean_object* v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v_stackSz_x3f_126_ = lean_ctor_get(v_a_125_, 1);
lean_inc(v_stackSz_x3f_126_);
lean_dec(v_a_125_);
v___x_127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_128_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_126_, v___x_127_);
lean_dec(v_stackSz_x3f_126_);
v___x_129_ = lean_bool_not(v___x_128_);
v_a_101_ = v___x_129_;
goto v___jp_100_;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_142_; 
lean_dec_ref(v_b_84_);
v_a_130_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_142_ == 0)
{
v___x_132_ = v___x_124_;
v_isShared_133_ = v_isSharedCheck_142_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_124_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_142_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_ref_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v_ref_134_ = lean_ctor_get(v___y_85_, 7);
v___x_135_ = lean_io_error_to_string(v_a_130_);
v___x_136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
v___x_137_ = l_Lean_MessageData_ofFormat(v___x_136_);
lean_inc(v_ref_134_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_ref_134_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_138_);
v___x_140_ = v___x_132_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_id_143_ = l_Lean_Syntax_getArg(v___x_97_, v___x_95_);
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_143_);
v___x_145_ = l_Lean_Syntax_isOfKind(v_id_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_dec(v_id_143_);
goto v___jp_98_;
}
else
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = l_Lean_Syntax_getArg(v___x_97_, v___x_96_);
v___x_147_ = l_Lean_Syntax_isNone(v___x_146_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
lean_inc(v___x_146_);
v___x_148_ = l_Lean_Syntax_matchesNull(v___x_146_, v___x_96_);
if (v___x_148_ == 0)
{
lean_dec(v___x_146_);
lean_dec(v_id_143_);
goto v___jp_98_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_150_ = l_Lean_Syntax_getArg(v___x_146_, v___x_95_);
lean_dec(v___x_146_);
v___x_151_ = l_Lean_Syntax_isOfKind(v___x_150_, v___x_149_);
if (v___x_151_ == 0)
{
lean_dec(v_id_143_);
goto v___jp_98_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box(0);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_143_, v___x_95_, v___x_152_, v___y_85_, v___y_86_);
lean_dec(v_id_143_);
v___y_103_ = v___x_153_;
goto v___jp_102_;
}
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_146_);
v___x_154_ = lean_box(0);
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_143_, v___x_95_, v___x_154_, v___y_85_, v___y_86_);
lean_dec(v_id_143_);
v___y_103_ = v___x_155_;
goto v___jp_102_;
}
}
}
v___jp_98_:
{
lean_object* v___x_99_; 
lean_inc(v___x_97_);
v___x_99_ = lean_array_push(v_b_84_, v___x_97_);
v_a_89_ = v___x_99_;
goto v___jp_88_;
}
v___jp_100_:
{
if (v_a_101_ == 0)
{
v_a_89_ = v_b_84_;
goto v___jp_88_;
}
else
{
goto v___jp_98_;
}
}
v___jp_102_:
{
if (lean_obj_tag(v___y_103_) == 0)
{
lean_object* v_a_104_; uint8_t v___x_105_; 
v_a_104_ = lean_ctor_get(v___y_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___y_103_, 1);
v___x_105_ = lean_unbox(v_a_104_);
lean_dec(v_a_104_);
v_a_101_ = v___x_105_;
goto v___jp_100_;
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec_ref(v_b_84_);
v_a_106_ = lean_ctor_get(v___y_103_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___y_103_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___y_103_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___y_103_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v_b_84_);
return v___x_156_;
}
v___jp_88_:
{
size_t v___x_90_; size_t v___x_91_; 
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_add(v_i_82_, v___x_90_);
v_i_82_ = v___x_91_;
v_b_84_ = v_a_89_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object* v_as_157_, lean_object* v_i_158_, lean_object* v_stop_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
size_t v_i_boxed_164_; size_t v_stop_boxed_165_; lean_object* v_res_166_; 
v_i_boxed_164_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_stop_boxed_165_ = lean_unbox_usize(v_stop_159_);
lean_dec(v_stop_159_);
v_res_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v_as_157_, v_i_boxed_164_, v_stop_boxed_165_, v_b_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v_as_157_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(lean_object* v_as_167_, size_t v_i_168_, size_t v_stop_169_, lean_object* v_b_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_a_175_; uint8_t v___x_179_; 
v___x_179_ = lean_usize_dec_eq(v_i_168_, v_stop_169_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v_a_187_; lean_object* v___y_189_; uint8_t v___x_200_; 
v___x_180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_array_uget_borrowed(v_as_167_, v_i_168_);
lean_inc(v___x_183_);
v___x_200_ = l_Lean_Syntax_isOfKind(v___x_183_, v___x_180_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_183_);
v___x_202_ = l_Lean_Syntax_isOfKind(v___x_183_, v___x_201_);
if (v___x_202_ == 0)
{
goto v___jp_184_;
}
else
{
lean_object* v_id_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_id_203_ = l_Lean_Syntax_getArg(v___x_183_, v___x_181_);
v___x_204_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_203_);
v___x_205_ = l_Lean_Syntax_isOfKind(v_id_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v_id_203_);
goto v___jp_184_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = l_Lean_Syntax_getArg(v___x_183_, v___x_206_);
v___x_208_ = l_Lean_Syntax_matchesNull(v___x_207_, v___x_182_);
if (v___x_208_ == 0)
{
lean_dec(v_id_203_);
goto v___jp_184_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = l_Lean_TSyntax_getId(v_id_203_);
lean_dec(v_id_203_);
v___x_210_ = l_Lean_Parser_getParserAliasInfo(v___x_209_);
lean_dec(v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v_stackSz_x3f_212_; lean_object* v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v_stackSz_x3f_212_ = lean_ctor_get(v_a_211_, 1);
lean_inc(v_stackSz_x3f_212_);
lean_dec(v_a_211_);
v___x_213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_214_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_212_, v___x_213_);
lean_dec(v_stackSz_x3f_212_);
v___x_215_ = lean_bool_not(v___x_214_);
v_a_187_ = v___x_215_;
goto v___jp_186_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_b_170_);
v_a_216_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_218_ = v___x_210_;
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_210_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v_ref_220_ = lean_ctor_get(v___y_171_, 7);
v___x_221_ = lean_io_error_to_string(v_a_216_);
v___x_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = l_Lean_MessageData_ofFormat(v___x_222_);
lean_inc(v_ref_220_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_220_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_224_);
v___x_226_ = v___x_218_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_id_229_ = l_Lean_Syntax_getArg(v___x_183_, v___x_181_);
v___x_230_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_229_);
v___x_231_ = l_Lean_Syntax_isOfKind(v_id_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec(v_id_229_);
goto v___jp_184_;
}
else
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = l_Lean_Syntax_getArg(v___x_183_, v___x_182_);
v___x_233_ = l_Lean_Syntax_isNone(v___x_232_);
if (v___x_233_ == 0)
{
uint8_t v___x_234_; 
lean_inc(v___x_232_);
v___x_234_ = l_Lean_Syntax_matchesNull(v___x_232_, v___x_182_);
if (v___x_234_ == 0)
{
lean_dec(v___x_232_);
lean_dec(v_id_229_);
goto v___jp_184_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_235_ = l_Lean_Syntax_getArg(v___x_232_, v___x_181_);
lean_dec(v___x_232_);
v___x_236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_237_ = l_Lean_Syntax_isOfKind(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_dec(v_id_229_);
goto v___jp_184_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_229_, v___x_181_, v___x_238_, v___y_171_, v___y_172_);
lean_dec(v_id_229_);
v___y_189_ = v___x_239_;
goto v___jp_188_;
}
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v___x_232_);
v___x_240_ = lean_box(0);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_229_, v___x_181_, v___x_240_, v___y_171_, v___y_172_);
lean_dec(v_id_229_);
v___y_189_ = v___x_241_;
goto v___jp_188_;
}
}
}
v___jp_184_:
{
lean_object* v___x_185_; 
lean_inc(v___x_183_);
v___x_185_ = lean_array_push(v_b_170_, v___x_183_);
v_a_175_ = v___x_185_;
goto v___jp_174_;
}
v___jp_186_:
{
if (v_a_187_ == 0)
{
v_a_175_ = v_b_170_;
goto v___jp_174_;
}
else
{
goto v___jp_184_;
}
}
v___jp_188_:
{
if (lean_obj_tag(v___y_189_) == 0)
{
lean_object* v_a_190_; uint8_t v___x_191_; 
v_a_190_ = lean_ctor_get(v___y_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___y_189_, 1);
v___x_191_ = lean_unbox(v_a_190_);
lean_dec(v_a_190_);
v_a_187_ = v___x_191_;
goto v___jp_186_;
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_b_170_);
v_a_192_ = lean_ctor_get(v___y_189_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___y_189_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___y_189_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___y_189_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v_b_170_);
return v___x_242_;
}
v___jp_174_:
{
size_t v___x_176_; size_t v___x_177_; 
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_add(v_i_168_, v___x_176_);
v_i_168_ = v___x_177_;
v_b_170_ = v_a_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object* v_as_243_, lean_object* v_i_244_, lean_object* v_stop_245_, lean_object* v_b_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
size_t v_i_boxed_250_; size_t v_stop_boxed_251_; lean_object* v_res_252_; 
v_i_boxed_250_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_stop_boxed_251_ = lean_unbox_usize(v_stop_245_);
lean_dec(v_stop_245_);
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v_as_243_, v_i_boxed_250_, v_stop_boxed_251_, v_b_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec_ref(v_as_243_);
return v_res_252_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(lean_object* v_opts_253_, lean_object* v_opt_254_){
_start:
{
lean_object* v_name_255_; lean_object* v_defValue_256_; lean_object* v_map_257_; lean_object* v___x_258_; 
v_name_255_ = lean_ctor_get(v_opt_254_, 0);
v_defValue_256_ = lean_ctor_get(v_opt_254_, 1);
v_map_257_ = lean_ctor_get(v_opts_253_, 0);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_257_, v_name_255_);
if (lean_obj_tag(v___x_258_) == 0)
{
uint8_t v___x_259_; 
v___x_259_ = lean_unbox(v_defValue_256_);
return v___x_259_;
}
else
{
lean_object* v_val_260_; 
v_val_260_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v___x_258_, 1);
if (lean_obj_tag(v_val_260_) == 1)
{
uint8_t v_v_261_; 
v_v_261_ = lean_ctor_get_uint8(v_val_260_, 0);
lean_dec_ref_known(v_val_260_, 0);
return v_v_261_;
}
else
{
uint8_t v___x_262_; 
lean_dec(v_val_260_);
v___x_262_ = lean_unbox(v_defValue_256_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_263_, lean_object* v_opt_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_263_, v_opt_264_);
lean_dec_ref(v_opt_264_);
lean_dec_ref(v_opts_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_box(1);
v___x_268_ = l_Lean_MessageData_ofFormat(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2));
v___x_273_ = l_Lean_MessageData_ofFormat(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
return v_x_274_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_299_; 
v_head_276_ = lean_ctor_get(v_x_275_, 0);
v_tail_277_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_299_ == 0)
{
v___x_279_ = v_x_275_;
v_isShared_280_ = v_isSharedCheck_299_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_inc(v_head_276_);
lean_dec(v_x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_299_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_before_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_297_; 
v_before_281_ = lean_ctor_get(v_head_276_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_head_276_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_head_276_, 1);
lean_dec(v_unused_298_);
v___x_283_ = v_head_276_;
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_before_281_);
lean_dec(v_head_276_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 7);
lean_ctor_set(v___x_283_, 1, v___x_285_);
lean_ctor_set(v___x_283_, 0, v_x_274_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_x_274_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_296_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 7);
lean_ctor_set(v___x_279_, 1, v___x_288_);
lean_ctor_set(v___x_279_, 0, v___x_287_);
v___x_290_ = v___x_279_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_295_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = l_Lean_MessageData_ofSyntax(v_before_281_);
v___x_292_ = l_Lean_indentD(v___x_291_);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_290_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v_x_274_ = v___x_293_;
v_x_275_ = v_tail_277_;
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
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1));
v___x_304_ = l_Lean_MessageData_ofFormat(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(lean_object* v_msgData_305_, lean_object* v_macroStack_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_scopes_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_opts_313_; lean_object* v___x_314_; uint8_t v___x_315_; uint8_t v___x_316_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_scopes_310_ = lean_ctor_get(v___x_309_, 2);
lean_inc(v_scopes_310_);
lean_dec(v___x_309_);
v___x_311_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_312_ = l_List_head_x21___redArg(v___x_311_, v_scopes_310_);
lean_dec(v_scopes_310_);
v_opts_313_ = lean_ctor_get(v___x_312_, 1);
lean_inc_ref(v_opts_313_);
lean_dec(v___x_312_);
v___x_314_ = l_Lean_Elab_pp_macroStack;
v___x_315_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_313_, v___x_314_);
lean_dec_ref(v_opts_313_);
v___x_316_ = lean_bool_not(v___x_315_);
if (v___x_316_ == 0)
{
if (lean_obj_tag(v_macroStack_306_) == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_msgData_305_);
return v___x_317_;
}
else
{
lean_object* v_head_318_; lean_object* v_after_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_334_; 
v_head_318_ = lean_ctor_get(v_macroStack_306_, 0);
lean_inc(v_head_318_);
v_after_319_ = lean_ctor_get(v_head_318_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_head_318_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_head_318_, 0);
lean_dec(v_unused_335_);
v___x_321_ = v_head_318_;
v_isShared_322_ = v_isSharedCheck_334_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_after_319_);
lean_dec(v_head_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_334_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 7);
lean_ctor_set(v___x_321_, 1, v___x_323_);
lean_ctor_set(v___x_321_, 0, v_msgData_305_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_msgData_305_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_333_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_msgData_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_326_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_MessageData_ofSyntax(v_after_319_);
v___x_329_ = l_Lean_indentD(v___x_328_);
v_msgData_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_330_, 0, v___x_327_);
lean_ctor_set(v_msgData_330_, 1, v___x_329_);
v___x_331_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(v_msgData_330_, v_macroStack_306_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
}
else
{
lean_object* v___x_336_; 
lean_dec(v_macroStack_306_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_msgData_305_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_337_, lean_object* v_macroStack_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_337_, v_macroStack_338_, v___y_339_);
lean_dec(v___y_339_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_342_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_ctor_set(v___x_347_, 2, v___x_346_);
lean_ctor_set(v___x_347_, 3, v___x_346_);
lean_ctor_set(v___x_347_, 4, v___x_345_);
lean_ctor_set(v___x_347_, 5, v___x_345_);
lean_ctor_set(v___x_347_, 6, v___x_345_);
lean_ctor_set(v___x_347_, 7, v___x_345_);
lean_ctor_set(v___x_347_, 8, v___x_345_);
lean_ctor_set(v___x_347_, 9, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_unsigned_to_nat(32u);
v___x_349_ = lean_mk_empty_array_with_capacity(v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = ((size_t)5ULL);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_unsigned_to_nat(32u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_356_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_352_);
lean_ctor_set(v___x_356_, 3, v___x_352_);
lean_ctor_set_usize(v___x_356_, 4, v___x_351_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_box(1);
v___x_358_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_359_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
lean_ctor_set(v___x_360_, 2, v___x_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_env_365_; lean_object* v___x_366_; lean_object* v_scopes_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_opts_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_364_ = lean_st_ref_get(v___y_362_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
v___x_366_ = lean_st_ref_get(v___y_362_);
v_scopes_367_ = lean_ctor_get(v___x_366_, 2);
lean_inc(v_scopes_367_);
lean_dec(v___x_366_);
v___x_368_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_369_ = l_List_head_x21___redArg(v___x_368_, v_scopes_367_);
lean_dec(v_scopes_367_);
v_opts_370_ = lean_ctor_get(v___x_369_, 1);
lean_inc_ref(v_opts_370_);
lean_dec(v___x_369_);
v___x_371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_372_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_373_, 0, v_env_365_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_372_);
lean_ctor_set(v___x_373_, 3, v_opts_370_);
v___x_374_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_msgData_361_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_376_, v___y_377_);
lean_dec(v___y_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Elab_Command_getRef___redArg(v___y_381_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v_macroStack_386_; lean_object* v___x_387_; lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_399_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v_macroStack_386_ = lean_ctor_get(v___y_381_, 4);
v___x_387_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_380_, v___y_382_);
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
v___x_389_ = l_Lean_Elab_getBetterRef(v_a_385_, v_macroStack_386_);
lean_dec(v_a_385_);
lean_inc(v_macroStack_386_);
v___x_390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_388_, v_macroStack_386_, v___y_382_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_399_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_389_);
lean_ctor_set(v___x_395_, 1, v_a_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 1);
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v_msg_380_);
v_a_400_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_384_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_384_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(lean_object* v_as_413_, size_t v_i_414_, size_t v_stop_415_, lean_object* v_b_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_a_421_; uint8_t v___x_425_; 
v___x_425_ = lean_usize_dec_eq(v_i_414_, v_stop_415_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v_a_431_; lean_object* v___y_433_; uint8_t v___x_444_; 
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_427_ = lean_array_uget_borrowed(v_as_413_, v_i_414_);
lean_inc(v___x_427_);
v___x_444_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_426_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_427_);
v___x_446_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_445_);
if (v___x_446_ == 0)
{
goto v___jp_428_;
}
else
{
lean_object* v___x_447_; lean_object* v_id_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v_id_448_ = l_Lean_Syntax_getArg(v___x_427_, v___x_447_);
v___x_449_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_448_);
v___x_450_ = l_Lean_Syntax_isOfKind(v_id_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec(v_id_448_);
goto v___jp_428_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = l_Lean_Syntax_getArg(v___x_427_, v___x_452_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_453_, v___x_451_);
if (v___x_454_ == 0)
{
lean_dec(v_id_448_);
goto v___jp_428_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = l_Lean_TSyntax_getId(v_id_448_);
lean_dec(v_id_448_);
v___x_456_ = l_Lean_Parser_getParserAliasInfo(v___x_455_);
lean_dec(v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_stackSz_x3f_458_; lean_object* v___x_459_; uint8_t v___x_460_; uint8_t v___x_461_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v_stackSz_x3f_458_ = lean_ctor_get(v_a_457_, 1);
lean_inc(v_stackSz_x3f_458_);
lean_dec(v_a_457_);
v___x_459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_460_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_458_, v___x_459_);
lean_dec(v_stackSz_x3f_458_);
v___x_461_ = lean_bool_not(v___x_460_);
v_a_431_ = v___x_461_;
goto v___jp_430_;
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_b_416_);
v_a_462_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_474_ == 0)
{
v___x_464_ = v___x_456_;
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_456_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_ref_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v_ref_466_ = lean_ctor_get(v___y_417_, 7);
v___x_467_ = lean_io_error_to_string(v_a_462_);
v___x_468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = l_Lean_MessageData_ofFormat(v___x_468_);
lean_inc(v_ref_466_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_ref_466_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_470_);
v___x_472_ = v___x_464_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v_id_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v_id_476_ = l_Lean_Syntax_getArg(v___x_427_, v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_476_);
v___x_478_ = l_Lean_Syntax_isOfKind(v_id_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v_id_476_);
goto v___jp_428_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = l_Lean_Syntax_getArg(v___x_427_, v___x_479_);
v___x_481_ = l_Lean_Syntax_isNone(v___x_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_matchesNull(v___x_480_, v___x_479_);
if (v___x_482_ == 0)
{
lean_dec(v___x_480_);
lean_dec(v_id_476_);
goto v___jp_428_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = l_Lean_Syntax_getArg(v___x_480_, v___x_475_);
lean_dec(v___x_480_);
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_485_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec(v_id_476_);
goto v___jp_428_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_476_, v___x_475_, v___x_486_, v___y_417_, v___y_418_);
lean_dec(v_id_476_);
v___y_433_ = v___x_487_;
goto v___jp_432_;
}
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v___x_480_);
v___x_488_ = lean_box(0);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_476_, v___x_475_, v___x_488_, v___y_417_, v___y_418_);
lean_dec(v_id_476_);
v___y_433_ = v___x_489_;
goto v___jp_432_;
}
}
}
v___jp_428_:
{
lean_object* v___x_429_; 
lean_inc(v___x_427_);
v___x_429_ = lean_array_push(v_b_416_, v___x_427_);
v_a_421_ = v___x_429_;
goto v___jp_420_;
}
v___jp_430_:
{
if (v_a_431_ == 0)
{
v_a_421_ = v_b_416_;
goto v___jp_420_;
}
else
{
goto v___jp_428_;
}
}
v___jp_432_:
{
if (lean_obj_tag(v___y_433_) == 0)
{
lean_object* v_a_434_; uint8_t v___x_435_; 
v_a_434_ = lean_ctor_get(v___y_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___y_433_, 1);
v___x_435_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
v_a_431_ = v___x_435_;
goto v___jp_430_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_b_416_);
v_a_436_ = lean_ctor_get(v___y_433_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___y_433_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___y_433_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___y_433_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_b_416_);
return v___x_490_;
}
v___jp_420_:
{
size_t v___x_422_; size_t v___x_423_; 
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_add(v_i_414_, v___x_422_);
v_i_414_ = v___x_423_;
v_b_416_ = v_a_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
size_t v_i_boxed_498_; size_t v_stop_boxed_499_; lean_object* v_res_500_; 
v_i_boxed_498_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_499_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v_as_491_, v_i_boxed_498_, v_stop_boxed_499_, v_b_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec_ref(v_as_491_);
return v_res_500_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_box(0);
v___x_514_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; uint8_t v___x_531_; 
v___x_527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_522_);
v___x_530_ = l_Lean_Syntax_isOfKind(v_a_522_, v___x_529_);
v___x_531_ = 1;
if (v___x_530_ == 0)
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_522_);
v___x_539_ = l_Lean_Syntax_isOfKind(v_a_522_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v_a_522_);
goto v___jp_532_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_a_545_; lean_object* v___y_551_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = l_Lean_Syntax_getArg(v_a_522_, v___x_540_);
lean_dec(v_a_522_);
v___x_542_ = l_Lean_Syntax_getArgs(v___x_541_);
lean_dec(v___x_541_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_size(v___x_542_);
v___x_562_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_563_ = lean_nat_dec_lt(v___x_543_, v___x_561_);
if (v___x_563_ == 0)
{
lean_dec_ref(v___x_542_);
v_a_545_ = v___x_562_;
goto v___jp_544_;
}
else
{
uint8_t v___x_564_; 
v___x_564_ = lean_nat_dec_le(v___x_561_, v___x_561_);
if (v___x_564_ == 0)
{
if (v___x_563_ == 0)
{
lean_dec_ref(v___x_542_);
v_a_545_ = v___x_562_;
goto v___jp_544_;
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = ((size_t)0ULL);
v___x_566_ = lean_usize_of_nat(v___x_561_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_542_, v___x_565_, v___x_566_, v___x_562_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_542_);
v___y_551_ = v___x_567_;
goto v___jp_550_;
}
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_561_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_542_, v___x_568_, v___x_569_, v___x_562_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_542_);
v___y_551_ = v___x_570_;
goto v___jp_550_;
}
}
v___jp_544_:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_array_get_size(v_a_545_);
v___x_547_ = lean_nat_dec_eq(v___x_546_, v___x_540_);
if (v___x_547_ == 0)
{
lean_dec_ref(v_a_545_);
goto v___jp_532_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_array_fget(v_a_545_, v___x_543_);
lean_dec_ref(v_a_545_);
v_a_522_ = v___x_548_;
goto _start;
}
}
v___jp_550_:
{
if (lean_obj_tag(v___y_551_) == 0)
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___y_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___y_551_, 1);
v_a_545_ = v_a_552_;
goto v___jp_544_;
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_523_);
v_a_553_ = lean_ctor_get(v___y_551_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___y_551_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___y_551_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___y_551_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___y_583_; lean_object* v___y_589_; lean_object* v_id_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v_id_599_ = l_Lean_Syntax_getArg(v_a_522_, v___x_571_);
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_599_);
v___x_602_ = l_Lean_Syntax_isOfKind(v_id_599_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
lean_dec(v_id_599_);
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_522_);
v___x_604_ = l_Lean_Syntax_isOfKind(v_a_522_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v_a_522_);
goto v___jp_594_;
}
else
{
lean_object* v___x_605_; lean_object* v_a_607_; lean_object* v___y_613_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_623_ = l_Lean_Syntax_getArg(v_a_522_, v___x_605_);
lean_dec(v_a_522_);
v___x_624_ = l_Lean_Syntax_getArgs(v___x_623_);
lean_dec(v___x_623_);
v___x_625_ = lean_array_get_size(v___x_624_);
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_627_ = lean_nat_dec_lt(v___x_571_, v___x_625_);
if (v___x_627_ == 0)
{
lean_dec_ref(v___x_624_);
v_a_607_ = v___x_626_;
goto v___jp_606_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_le(v___x_625_, v___x_625_);
if (v___x_628_ == 0)
{
if (v___x_627_ == 0)
{
lean_dec_ref(v___x_624_);
v_a_607_ = v___x_626_;
goto v___jp_606_;
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_625_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_624_, v___x_629_, v___x_630_, v___x_626_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_624_);
v___y_613_ = v___x_631_;
goto v___jp_612_;
}
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_625_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_624_, v___x_632_, v___x_633_, v___x_626_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_624_);
v___y_613_ = v___x_634_;
goto v___jp_612_;
}
}
v___jp_606_:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_array_get_size(v_a_607_);
v___x_609_ = lean_nat_dec_eq(v___x_608_, v___x_605_);
if (v___x_609_ == 0)
{
lean_dec_ref(v_a_607_);
goto v___jp_594_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_array_fget(v_a_607_, v___x_571_);
lean_dec_ref(v_a_607_);
v_a_522_ = v___x_610_;
goto _start;
}
}
v___jp_612_:
{
if (lean_obj_tag(v___y_613_) == 0)
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v___y_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___y_613_, 1);
v_a_607_ = v_a_614_;
goto v___jp_606_;
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_a_523_);
v_a_615_ = lean_ctor_get(v___y_613_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___y_613_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___y_613_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___y_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
else
{
lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___x_717_; lean_object* v_a_719_; lean_object* v___y_725_; lean_object* v_a_736_; lean_object* v___y_742_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_752_ = l_Lean_Syntax_getArg(v_a_522_, v___x_717_);
v___x_753_ = l_Lean_Syntax_isNone(v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
lean_inc(v___x_752_);
v___x_754_ = l_Lean_Syntax_matchesNull(v___x_752_, v___x_717_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; uint8_t v___x_756_; 
lean_dec(v_id_599_);
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_756_ = l_Lean_Syntax_isOfKind(v_a_522_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v___x_752_);
goto v___jp_577_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_757_ = l_Lean_Syntax_getArgs(v___x_752_);
lean_dec(v___x_752_);
v___x_758_ = lean_array_get_size(v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_760_ = lean_nat_dec_lt(v___x_571_, v___x_758_);
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_757_);
v_a_736_ = v___x_759_;
goto v___jp_735_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_le(v___x_758_, v___x_758_);
if (v___x_761_ == 0)
{
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_757_);
v_a_736_ = v___x_759_;
goto v___jp_735_;
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_758_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_757_, v___x_762_, v___x_763_, v___x_759_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_757_);
v___y_742_ = v___x_764_;
goto v___jp_741_;
}
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_758_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_757_, v___x_765_, v___x_766_, v___x_759_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_757_);
v___y_742_ = v___x_767_;
goto v___jp_741_;
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = l_Lean_Syntax_getArg(v___x_752_, v___x_571_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_770_ = l_Lean_Syntax_isOfKind(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
lean_dec(v_id_599_);
v___x_771_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_772_ = l_Lean_Syntax_isOfKind(v_a_522_, v___x_771_);
if (v___x_772_ == 0)
{
lean_dec(v___x_752_);
goto v___jp_572_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_773_ = l_Lean_Syntax_getArgs(v___x_752_);
lean_dec(v___x_752_);
v___x_774_ = lean_array_get_size(v___x_773_);
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_776_ = lean_nat_dec_lt(v___x_571_, v___x_774_);
if (v___x_776_ == 0)
{
lean_dec_ref(v___x_773_);
v_a_719_ = v___x_775_;
goto v___jp_718_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_777_ == 0)
{
if (v___x_776_ == 0)
{
lean_dec_ref(v___x_773_);
v_a_719_ = v___x_775_;
goto v___jp_718_;
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_of_nat(v___x_774_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_773_, v___x_778_, v___x_779_, v___x_775_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_773_);
v___y_725_ = v___x_780_;
goto v___jp_724_;
}
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_774_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_773_, v___x_781_, v___x_782_, v___x_775_, v_a_524_, v_a_525_);
lean_dec_ref(v___x_773_);
v___y_725_ = v___x_783_;
goto v___jp_724_;
}
}
}
}
else
{
lean_dec(v___x_752_);
lean_dec(v_a_522_);
v___y_636_ = v_a_524_;
v___y_637_ = v_a_525_;
goto v___jp_635_;
}
}
}
else
{
lean_dec(v___x_752_);
lean_dec(v_a_522_);
v___y_636_ = v_a_524_;
v___y_637_ = v_a_525_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_inc(v_id_599_);
v___x_638_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_638_, 0, v_id_599_);
v___x_639_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_638_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_708_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_708_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_708_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_708_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
if (lean_obj_tag(v_a_640_) == 1)
{
lean_object* v_val_644_; 
v_val_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v_a_640_, 1);
switch(lean_obj_tag(v_val_644_))
{
case 0:
{
lean_object* v_cat_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
lean_dec(v_id_599_);
v_cat_645_ = lean_ctor_get(v_val_644_, 0);
lean_inc(v_cat_645_);
lean_dec_ref_known(v_val_644_, 1);
v___x_646_ = lean_box(0);
v___x_647_ = l_Lean_Syntax_mkAntiquotNode(v_cat_645_, v_a_523_, v___x_571_, v___x_646_, v___x_531_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_647_);
v___x_649_ = v___x_642_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
case 1:
{
lean_object* v_decl_651_; 
lean_del_object(v___x_642_);
lean_dec(v_id_599_);
v_decl_651_ = lean_ctor_get(v_val_644_, 0);
lean_inc(v_decl_651_);
lean_dec_ref_known(v_val_644_, 1);
if (lean_obj_tag(v_decl_651_) == 1)
{
lean_object* v_pre_652_; 
v_pre_652_ = lean_ctor_get(v_decl_651_, 0);
if (lean_obj_tag(v_pre_652_) == 1)
{
lean_object* v_pre_653_; 
v_pre_653_ = lean_ctor_get(v_pre_652_, 0);
if (lean_obj_tag(v_pre_653_) == 1)
{
lean_object* v_pre_654_; 
v_pre_654_ = lean_ctor_get(v_pre_653_, 0);
switch(lean_obj_tag(v_pre_654_))
{
case 0:
{
lean_object* v_str_655_; lean_object* v_str_656_; lean_object* v_str_657_; uint8_t v___x_658_; 
v_str_655_ = lean_ctor_get(v_decl_651_, 1);
v_str_656_ = lean_ctor_get(v_pre_652_, 1);
v_str_657_ = lean_ctor_get(v_pre_653_, 1);
v___x_658_ = lean_string_dec_eq(v_str_657_, v___x_527_);
if (v___x_658_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = lean_string_dec_eq(v_str_656_, v___x_528_);
if (v___x_659_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_string_dec_eq(v_str_655_, v___x_600_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_662_ = lean_string_dec_eq(v_str_655_, v___x_661_);
if (v___x_662_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
lean_object* v___x_663_; 
lean_dec_ref_known(v_decl_651_, 2);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_583_ = v___x_663_;
goto v___jp_582_;
}
}
else
{
lean_object* v___x_664_; 
lean_dec_ref_known(v_decl_651_, 2);
v___x_664_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_583_ = v___x_664_;
goto v___jp_582_;
}
}
}
}
case 1:
{
lean_object* v_pre_665_; 
v_pre_665_ = lean_ctor_get(v_pre_654_, 0);
if (lean_obj_tag(v_pre_665_) == 0)
{
lean_object* v_str_666_; lean_object* v_str_667_; lean_object* v_str_668_; lean_object* v_str_669_; uint8_t v___x_670_; 
v_str_666_ = lean_ctor_get(v_decl_651_, 1);
v_str_667_ = lean_ctor_get(v_pre_652_, 1);
v_str_668_ = lean_ctor_get(v_pre_653_, 1);
v_str_669_ = lean_ctor_get(v_pre_654_, 1);
v___x_670_ = lean_string_dec_eq(v_str_669_, v___x_527_);
if (v___x_670_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = lean_string_dec_eq(v_str_668_, v___x_528_);
if (v___x_671_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_673_ = lean_string_dec_eq(v_str_667_, v___x_672_);
if (v___x_673_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = lean_string_dec_eq(v_str_666_, v___x_600_);
if (v___x_674_ == 0)
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
else
{
lean_object* v___x_675_; 
lean_dec_ref_known(v_decl_651_, 2);
v___x_675_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_583_ = v___x_675_;
goto v___jp_582_;
}
}
}
}
}
else
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
}
default: 
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
}
}
else
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
}
else
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
}
else
{
v___y_583_ = v_decl_651_;
goto v___jp_582_;
}
}
default: 
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_642_);
v_isSharedCheck_700_ = !lean_is_exclusive(v_val_644_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_val_644_, 0);
lean_dec(v_unused_701_);
v___x_677_ = v_val_644_;
v_isShared_678_ = v_isSharedCheck_700_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_val_644_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_700_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = l_Lean_TSyntax_getId(v_id_599_);
lean_dec(v_id_599_);
v___x_680_ = l_Lean_Name_eraseMacroScopes(v___x_679_);
lean_dec(v___x_679_);
v___x_681_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_680_);
lean_dec(v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; 
lean_del_object(v___x_677_);
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
if (lean_obj_tag(v_a_682_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
v___y_589_ = v___x_683_;
goto v___jp_588_;
}
else
{
lean_object* v_val_684_; 
v_val_684_ = lean_ctor_get(v_a_682_, 0);
lean_inc(v_val_684_);
lean_dec_ref_known(v_a_682_, 1);
v___y_589_ = v_val_684_;
goto v___jp_588_;
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_a_523_);
v_a_685_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_699_ == 0)
{
v___x_687_ = v___x_681_;
v_isShared_688_ = v_isSharedCheck_699_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_699_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_ref_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v_ref_689_ = lean_ctor_get(v___y_636_, 7);
v___x_690_ = lean_io_error_to_string(v_a_685_);
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 3);
lean_ctor_set(v___x_677_, 0, v___x_690_);
v___x_692_ = v___x_677_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_698_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = l_Lean_MessageData_ofFormat(v___x_692_);
lean_inc(v_ref_689_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_ref_689_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_694_);
v___x_696_ = v___x_687_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
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
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_642_);
lean_dec(v_a_640_);
lean_dec(v_a_523_);
v___x_702_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_703_ = l_Lean_MessageData_ofSyntax(v_id_599_);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_706_, v___y_636_, v___y_637_);
return v___x_707_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_id_599_);
lean_dec(v_a_523_);
v_a_709_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_639_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_639_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
v___jp_718_:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_get_size(v_a_719_);
v___x_721_ = lean_nat_dec_eq(v___x_720_, v___x_717_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_a_719_);
goto v___jp_572_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_array_fget(v_a_719_, v___x_571_);
lean_dec_ref(v_a_719_);
v_a_522_ = v___x_722_;
goto _start;
}
}
v___jp_724_:
{
if (lean_obj_tag(v___y_725_) == 0)
{
lean_object* v_a_726_; 
v_a_726_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___y_725_, 1);
v_a_719_ = v_a_726_;
goto v___jp_718_;
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_523_);
v_a_727_ = lean_ctor_get(v___y_725_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___y_725_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___y_725_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___y_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
v___jp_735_:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_array_get_size(v_a_736_);
v___x_738_ = lean_nat_dec_eq(v___x_737_, v___x_717_);
if (v___x_738_ == 0)
{
lean_dec_ref(v_a_736_);
goto v___jp_577_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = lean_array_fget(v_a_736_, v___x_571_);
lean_dec_ref(v_a_736_);
v_a_522_ = v___x_739_;
goto _start;
}
}
v___jp_741_:
{
if (lean_obj_tag(v___y_742_) == 0)
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___y_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___y_742_, 1);
v_a_736_ = v_a_743_;
goto v___jp_735_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_523_);
v_a_744_ = lean_ctor_get(v___y_742_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___y_742_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___y_742_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___y_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
v___jp_572_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_box(0);
v___x_575_ = l_Lean_Syntax_mkAntiquotNode(v___x_573_, v_a_523_, v___x_571_, v___x_574_, v___x_531_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
v___jp_577_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_box(0);
v___x_580_ = l_Lean_Syntax_mkAntiquotNode(v___x_578_, v_a_523_, v___x_571_, v___x_579_, v___x_531_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
v___jp_582_:
{
lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = lean_box(0);
v___x_585_ = 0;
v___x_586_ = l_Lean_Syntax_mkAntiquotNode(v___y_583_, v_a_523_, v___x_571_, v___x_584_, v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
v___jp_588_:
{
lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = lean_box(0);
v___x_591_ = 0;
v___x_592_ = l_Lean_Syntax_mkAntiquotNode(v___y_589_, v_a_523_, v___x_571_, v___x_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
v___jp_594_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_box(0);
v___x_597_ = l_Lean_Syntax_mkAntiquotNode(v___x_595_, v_a_523_, v___x_571_, v___x_596_, v___x_531_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
v___jp_532_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_box(0);
v___x_536_ = l_Lean_Syntax_mkAntiquotNode(v___x_533_, v_a_523_, v___x_534_, v___x_535_, v___x_531_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_790_, v___y_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_800_, lean_object* v_msg_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_806_, v_msg_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_812_, lean_object* v_macroStack_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_812_, v_macroStack_813_, v___y_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_818_, lean_object* v_macroStack_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_818_, v_macroStack_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_827_, lean_object* v_stx_828_, lean_object* v_id_829_, lean_object* v_suffix_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_828_, v_id_829_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_849_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_849_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_849_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_849_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_839_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_827_, v_a_835_, v_suffix_830_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_array_push(v___x_841_, v___x_839_);
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_844_ = lean_box(2);
v___x_845_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_843_);
lean_ctor_set(v___x_845_, 2, v___x_842_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_845_);
v___x_847_ = v___x_837_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_dec_ref(v_suffix_830_);
lean_dec(v_kind_827_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_850_, lean_object* v_stx_851_, lean_object* v_id_852_, lean_object* v_suffix_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_850_, v_stx_851_, v_id_852_, v_suffix_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_env_861_; lean_object* v___x_862_; lean_object* v_mainModule_863_; lean_object* v___x_864_; 
v___x_860_ = lean_st_ref_get(v___y_858_);
v_env_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_env_861_);
lean_dec(v___x_860_);
v___x_862_ = l_Lean_Environment_header(v_env_861_);
lean_dec_ref(v_env_861_);
v_mainModule_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_mainModule_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v_mainModule_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_865_);
lean_dec(v___y_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_879_ = lean_panic_fn_borrowed(v___x_878_, v_msg_877_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Lean_maxRecDepthErrorMessage;
v___x_886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_888_ = l_Lean_MessageData_ofFormat(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_890_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_891_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_ref_892_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_900_, lean_object* v_declName_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_904_; lean_object* v_env_905_; lean_object* v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; 
v___x_904_ = 0;
v_env_905_ = l_Lean_Environment_setExporting(v_env_900_, v___x_904_);
lean_inc(v_declName_901_);
v___x_906_ = l_Lean_mkPrivateName(v_env_905_, v_declName_901_);
v___x_907_ = 1;
lean_inc_ref(v_env_905_);
v___x_908_ = l_Lean_Environment_contains(v_env_905_, v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = l_Lean_privateToUserName(v_declName_901_);
v___x_910_ = l_Lean_Environment_contains(v_env_905_, v___x_909_, v___x_907_);
v___x_911_ = lean_box(v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___y_903_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v_env_905_);
lean_dec(v_declName_901_);
v___x_913_ = lean_box(v___x_908_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___y_903_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_915_, lean_object* v_declName_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_915_, v_declName_916_, v___y_917_, v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_920_, lean_object* v_i_921_, lean_object* v_k_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_keys_920_);
v___x_924_ = lean_nat_dec_lt(v_i_921_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_i_921_);
return v___x_924_;
}
else
{
lean_object* v_k_x27_925_; uint8_t v___x_926_; 
v_k_x27_925_ = lean_array_fget_borrowed(v_keys_920_, v_i_921_);
v___x_926_ = l_Lean_instBEqExtraModUse_beq(v_k_922_, v_k_x27_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_i_921_, v___x_927_);
lean_dec(v_i_921_);
v_i_921_ = v___x_928_;
goto _start;
}
else
{
lean_dec(v_i_921_);
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_930_, lean_object* v_i_931_, lean_object* v_k_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_930_, v_i_931_, v_k_932_);
lean_dec_ref(v_k_932_);
lean_dec_ref(v_keys_930_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_935_, size_t v_x_936_, lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
lean_object* v_es_938_; lean_object* v___x_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v_j_942_; lean_object* v___x_943_; 
v_es_938_ = lean_ctor_get(v_x_935_, 0);
v___x_939_ = lean_box(2);
v___x_940_ = ((size_t)31ULL);
v___x_941_ = lean_usize_land(v_x_936_, v___x_940_);
v_j_942_ = lean_usize_to_nat(v___x_941_);
v___x_943_ = lean_array_get_borrowed(v___x_939_, v_es_938_, v_j_942_);
lean_dec(v_j_942_);
switch(lean_obj_tag(v___x_943_))
{
case 0:
{
lean_object* v_key_944_; uint8_t v___x_945_; 
v_key_944_ = lean_ctor_get(v___x_943_, 0);
v___x_945_ = l_Lean_instBEqExtraModUse_beq(v_x_937_, v_key_944_);
return v___x_945_;
}
case 1:
{
lean_object* v_node_946_; size_t v___x_947_; size_t v___x_948_; 
v_node_946_ = lean_ctor_get(v___x_943_, 0);
v___x_947_ = ((size_t)5ULL);
v___x_948_ = lean_usize_shift_right(v_x_936_, v___x_947_);
v_x_935_ = v_node_946_;
v_x_936_ = v___x_948_;
goto _start;
}
default: 
{
uint8_t v___x_950_; 
v___x_950_ = 0;
return v___x_950_;
}
}
}
else
{
lean_object* v_ks_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_ks_951_ = lean_ctor_get(v_x_935_, 0);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_951_, v___x_952_, v_x_937_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
size_t v_x_84800__boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v_x_84800__boxed_957_ = lean_unbox_usize(v_x_955_);
lean_dec(v_x_955_);
v_res_958_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_954_, v_x_84800__boxed_957_, v_x_956_);
lean_dec_ref(v_x_956_);
lean_dec_ref(v_x_954_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
uint64_t v___x_962_; size_t v___x_963_; uint8_t v___x_964_; 
v___x_962_ = l_Lean_instHashableExtraModUse_hash(v_x_961_);
v___x_963_ = lean_uint64_to_usize(v___x_962_);
v___x_964_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_960_, v___x_963_, v_x_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_965_, v_x_966_);
lean_dec_ref(v_x_966_);
lean_dec_ref(v_x_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_969_; double v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_float_of_nat(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_973_, lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Elab_Command_getRef___redArg(v___y_975_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1027_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_974_, v___y_976_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1027_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1027_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v_traceState_986_; lean_object* v_env_987_; lean_object* v_messages_988_; lean_object* v_scopes_989_; lean_object* v_usedQuotCtxts_990_; lean_object* v_nextMacroScope_991_; lean_object* v_maxRecDepth_992_; lean_object* v_ngen_993_; lean_object* v_auxDeclNGen_994_; lean_object* v_infoState_995_; lean_object* v_snapshotTasks_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1026_; 
v___x_985_ = lean_st_ref_take(v___y_976_);
v_traceState_986_ = lean_ctor_get(v___x_985_, 9);
v_env_987_ = lean_ctor_get(v___x_985_, 0);
v_messages_988_ = lean_ctor_get(v___x_985_, 1);
v_scopes_989_ = lean_ctor_get(v___x_985_, 2);
v_usedQuotCtxts_990_ = lean_ctor_get(v___x_985_, 3);
v_nextMacroScope_991_ = lean_ctor_get(v___x_985_, 4);
v_maxRecDepth_992_ = lean_ctor_get(v___x_985_, 5);
v_ngen_993_ = lean_ctor_get(v___x_985_, 6);
v_auxDeclNGen_994_ = lean_ctor_get(v___x_985_, 7);
v_infoState_995_ = lean_ctor_get(v___x_985_, 8);
v_snapshotTasks_996_ = lean_ctor_get(v___x_985_, 10);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_998_ = v___x_985_;
v_isShared_999_ = v_isSharedCheck_1026_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_snapshotTasks_996_);
lean_inc(v_traceState_986_);
lean_inc(v_infoState_995_);
lean_inc(v_auxDeclNGen_994_);
lean_inc(v_ngen_993_);
lean_inc(v_maxRecDepth_992_);
lean_inc(v_nextMacroScope_991_);
lean_inc(v_usedQuotCtxts_990_);
lean_inc(v_scopes_989_);
lean_inc(v_messages_988_);
lean_inc(v_env_987_);
lean_dec(v___x_985_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1026_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
uint64_t v_tid_1000_; lean_object* v_traces_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1025_; 
v_tid_1000_ = lean_ctor_get_uint64(v_traceState_986_, sizeof(void*)*1);
v_traces_1001_ = lean_ctor_get(v_traceState_986_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_traceState_986_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1003_ = v_traceState_986_;
v_isShared_1004_ = v_isSharedCheck_1025_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_traces_1001_);
lean_dec(v_traceState_986_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1025_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; double v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_1007_ = 0;
v___x_1008_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1009_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1009_, 0, v_cls_973_);
lean_ctor_set(v___x_1009_, 1, v___x_1005_);
lean_ctor_set(v___x_1009_, 2, v___x_1008_);
lean_ctor_set_float(v___x_1009_, sizeof(void*)*3, v___x_1006_);
lean_ctor_set_float(v___x_1009_, sizeof(void*)*3 + 8, v___x_1006_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*3 + 16, v___x_1007_);
v___x_1010_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_1011_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v_a_981_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_a_979_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_PersistentArray_push___redArg(v_traces_1001_, v___x_1012_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1013_);
v___x_1015_ = v___x_1003_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1013_);
lean_ctor_set_uint64(v_reuseFailAlloc_1024_, sizeof(void*)*1, v_tid_1000_);
v___x_1015_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 9, v___x_1015_);
v___x_1017_ = v___x_998_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_env_987_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_messages_988_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_scopes_989_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_usedQuotCtxts_990_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_nextMacroScope_991_);
lean_ctor_set(v_reuseFailAlloc_1023_, 5, v_maxRecDepth_992_);
lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_ngen_993_);
lean_ctor_set(v_reuseFailAlloc_1023_, 7, v_auxDeclNGen_994_);
lean_ctor_set(v_reuseFailAlloc_1023_, 8, v_infoState_995_);
lean_ctor_set(v_reuseFailAlloc_1023_, 9, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 10, v_snapshotTasks_996_);
v___x_1017_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = lean_st_ref_set(v___y_976_, v___x_1017_);
v___x_1019_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1019_);
v___x_1021_ = v___x_983_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_msg_974_);
lean_dec(v_cls_973_);
v_a_1028_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_978_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_978_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1036_, lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1036_, v_msg_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1041_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1));
v___x_1045_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0));
v___x_1046_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1045_, v___x_1044_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v_cls_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_cls_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4));
v___x_1060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1061_ = l_Lean_Name_append(v___x_1060_, v_cls_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1072_, uint8_t v_isMeta_1073_, lean_object* v_hint_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_env_1079_; uint8_t v_isExporting_1080_; lean_object* v___x_1081_; lean_object* v_env_1082_; lean_object* v___x_1083_; lean_object* v_entry_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___y_1089_; lean_object* v___x_1115_; uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1078_ = lean_st_ref_get(v___y_1076_);
v_env_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_env_1079_);
lean_dec(v___x_1078_);
v_isExporting_1080_ = lean_ctor_get_uint8(v_env_1079_, sizeof(void*)*8);
lean_dec_ref(v_env_1079_);
v___x_1081_ = lean_st_ref_get(v___y_1076_);
v_env_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_env_1082_);
lean_dec(v___x_1081_);
v___x_1083_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2);
lean_inc(v_mod_1072_);
v_entry_1084_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1084_, 0, v_mod_1072_);
lean_ctor_set_uint8(v_entry_1084_, sizeof(void*)*1, v_isExporting_1080_);
lean_ctor_set_uint8(v_entry_1084_, sizeof(void*)*1 + 1, v_isMeta_1073_);
v___x_1085_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1086_ = lean_box(1);
v___x_1087_ = lean_box(0);
v___x_1115_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1083_, v___x_1085_, v_env_1082_, v___x_1086_, v___x_1087_);
v___x_1116_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1115_, v_entry_1084_);
lean_dec(v___x_1115_);
v___x_1117_ = lean_bool_not(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref_known(v_entry_1084_, 1);
lean_dec(v_hint_1074_);
lean_dec(v_mod_1072_);
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_scopes_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_opts_1126_; uint8_t v_hasTrace_1127_; 
v___x_1120_ = l_Lean_inheritedTraceOptions;
v___x_1121_ = lean_st_ref_get(v___x_1120_);
v___x_1122_ = lean_st_ref_get(v___y_1076_);
v_scopes_1123_ = lean_ctor_get(v___x_1122_, 2);
lean_inc(v_scopes_1123_);
lean_dec(v___x_1122_);
v___x_1124_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1125_ = l_List_head_x21___redArg(v___x_1124_, v_scopes_1123_);
lean_dec(v_scopes_1123_);
v_opts_1126_ = lean_ctor_get(v___x_1125_, 1);
lean_inc_ref(v_opts_1126_);
lean_dec(v___x_1125_);
v_hasTrace_1127_ = lean_ctor_get_uint8(v_opts_1126_, sizeof(void*)*1);
if (v_hasTrace_1127_ == 0)
{
lean_dec_ref(v_opts_1126_);
lean_dec(v___x_1121_);
lean_dec(v_hint_1074_);
lean_dec(v_mod_1072_);
v___y_1089_ = v___y_1076_;
goto v___jp_1088_;
}
else
{
lean_object* v_cls_1128_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_cls_1128_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4));
v___x_1149_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
v___x_1150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1121_, v_opts_1126_, v___x_1149_);
lean_dec_ref(v_opts_1126_);
lean_dec(v___x_1121_);
if (v___x_1150_ == 0)
{
lean_dec(v_hint_1074_);
lean_dec(v_mod_1072_);
v___y_1089_ = v___y_1076_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1151_; lean_object* v___y_1153_; 
v___x_1151_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
if (v_isExporting_1080_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__18));
v___y_1153_ = v___x_1160_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__19));
v___y_1153_ = v___x_1161_;
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_inc_ref(v___y_1153_);
v___x_1154_ = l_Lean_stringToMessageData(v___y_1153_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
if (v_isMeta_1073_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1135_ = v___x_1157_;
v___y_1136_ = v___x_1158_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1135_ = v___x_1157_;
v___y_1136_ = v___x_1159_;
goto v___jp_1134_;
}
}
}
v___jp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___y_1130_);
lean_ctor_set(v___x_1132_, 1, v___y_1131_);
v___x_1133_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1128_, v___x_1132_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref_known(v___x_1133_, 1);
v___y_1089_ = v___y_1076_;
goto v___jp_1088_;
}
else
{
lean_dec_ref_known(v_entry_1084_, 1);
return v___x_1133_;
}
}
v___jp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
lean_inc_ref(v___y_1136_);
v___x_1137_ = l_Lean_stringToMessageData(v___y_1136_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___y_1135_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_MessageData_ofName(v_mod_1072_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_Name_isAnonymous(v_hint_1074_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8);
v___x_1145_ = l_Lean_MessageData_ofName(v_hint_1074_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___y_1130_ = v___x_1142_;
v___y_1131_ = v___x_1146_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec(v_hint_1074_);
v___x_1147_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
v___y_1130_ = v___x_1142_;
v___y_1131_ = v___x_1148_;
goto v___jp_1129_;
}
}
}
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v_toEnvExtension_1091_; lean_object* v_env_1092_; lean_object* v_messages_1093_; lean_object* v_scopes_1094_; lean_object* v_usedQuotCtxts_1095_; lean_object* v_nextMacroScope_1096_; lean_object* v_maxRecDepth_1097_; lean_object* v_ngen_1098_; lean_object* v_auxDeclNGen_1099_; lean_object* v_infoState_1100_; lean_object* v_traceState_1101_; lean_object* v_snapshotTasks_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1114_; 
v___x_1090_ = lean_st_ref_take(v___y_1089_);
v_toEnvExtension_1091_ = lean_ctor_get(v___x_1085_, 0);
v_env_1092_ = lean_ctor_get(v___x_1090_, 0);
v_messages_1093_ = lean_ctor_get(v___x_1090_, 1);
v_scopes_1094_ = lean_ctor_get(v___x_1090_, 2);
v_usedQuotCtxts_1095_ = lean_ctor_get(v___x_1090_, 3);
v_nextMacroScope_1096_ = lean_ctor_get(v___x_1090_, 4);
v_maxRecDepth_1097_ = lean_ctor_get(v___x_1090_, 5);
v_ngen_1098_ = lean_ctor_get(v___x_1090_, 6);
v_auxDeclNGen_1099_ = lean_ctor_get(v___x_1090_, 7);
v_infoState_1100_ = lean_ctor_get(v___x_1090_, 8);
v_traceState_1101_ = lean_ctor_get(v___x_1090_, 9);
v_snapshotTasks_1102_ = lean_ctor_get(v___x_1090_, 10);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1104_ = v___x_1090_;
v_isShared_1105_ = v_isSharedCheck_1114_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_snapshotTasks_1102_);
lean_inc(v_traceState_1101_);
lean_inc(v_infoState_1100_);
lean_inc(v_auxDeclNGen_1099_);
lean_inc(v_ngen_1098_);
lean_inc(v_maxRecDepth_1097_);
lean_inc(v_nextMacroScope_1096_);
lean_inc(v_usedQuotCtxts_1095_);
lean_inc(v_scopes_1094_);
lean_inc(v_messages_1093_);
lean_inc(v_env_1092_);
lean_dec(v___x_1090_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1114_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_asyncMode_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v_asyncMode_1106_ = lean_ctor_get(v_toEnvExtension_1091_, 2);
v___x_1107_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1085_, v_env_1092_, v_entry_1084_, v_asyncMode_1106_, v___x_1087_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_messages_1093_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_scopes_1094_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_usedQuotCtxts_1095_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_nextMacroScope_1096_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v_maxRecDepth_1097_);
lean_ctor_set(v_reuseFailAlloc_1113_, 6, v_ngen_1098_);
lean_ctor_set(v_reuseFailAlloc_1113_, 7, v_auxDeclNGen_1099_);
lean_ctor_set(v_reuseFailAlloc_1113_, 8, v_infoState_1100_);
lean_ctor_set(v_reuseFailAlloc_1113_, 9, v_traceState_1101_);
lean_ctor_set(v_reuseFailAlloc_1113_, 10, v_snapshotTasks_1102_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_st_ref_set(v___y_1089_, v___x_1109_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1162_, lean_object* v_isMeta_1163_, lean_object* v_hint_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v_isMeta_boxed_1168_; lean_object* v_res_1169_; 
v_isMeta_boxed_1168_ = lean_unbox(v_isMeta_1163_);
v_res_1169_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1162_, v_isMeta_boxed_1168_, v_hint_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1170_, lean_object* v_declName_1171_, lean_object* v_as_1172_, size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec(v_declName_1171_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_b_1175_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v_modules_1182_; lean_object* v___x_1183_; lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v_toImport_1186_; lean_object* v_module_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1181_ = l_Lean_Environment_header(v___x_1170_);
v_modules_1182_ = lean_ctor_get(v___x_1181_, 3);
lean_inc_ref(v_modules_1182_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1184_ = lean_array_uget_borrowed(v_as_1172_, v_i_1174_);
v___x_1185_ = lean_array_get(v___x_1183_, v_modules_1182_, v_a_1184_);
lean_dec_ref(v_modules_1182_);
v_toImport_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_toImport_1186_);
lean_dec(v___x_1185_);
v_module_1187_ = lean_ctor_get(v_toImport_1186_, 0);
lean_inc(v_module_1187_);
lean_dec_ref(v_toImport_1186_);
v___x_1188_ = 0;
lean_inc(v_declName_1171_);
v___x_1189_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1187_, v___x_1188_, v_declName_1171_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; 
lean_dec_ref_known(v___x_1189_, 1);
v___x_1190_ = lean_box(0);
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_add(v_i_1174_, v___x_1191_);
v_i_1174_ = v___x_1192_;
v_b_1175_ = v___x_1190_;
goto _start;
}
else
{
lean_dec(v_declName_1171_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1194_, lean_object* v_declName_1195_, lean_object* v_as_1196_, lean_object* v_sz_1197_, lean_object* v_i_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
size_t v_sz_boxed_1203_; size_t v_i_boxed_1204_; lean_object* v_res_1205_; 
v_sz_boxed_1203_ = lean_unbox_usize(v_sz_1197_);
lean_dec(v_sz_1197_);
v_i_boxed_1204_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_res_1205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1194_, v_declName_1195_, v_as_1196_, v_sz_boxed_1203_, v_i_boxed_1204_, v_b_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_as_1196_);
lean_dec_ref(v___x_1194_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1206_, lean_object* v_x_1207_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
else
{
lean_object* v_key_1209_; lean_object* v_value_1210_; lean_object* v_tail_1211_; uint8_t v___x_1212_; 
v_key_1209_ = lean_ctor_get(v_x_1207_, 0);
v_value_1210_ = lean_ctor_get(v_x_1207_, 1);
v_tail_1211_ = lean_ctor_get(v_x_1207_, 2);
v___x_1212_ = lean_name_eq(v_key_1209_, v_a_1206_);
if (v___x_1212_ == 0)
{
v_x_1207_ = v_tail_1211_;
goto _start;
}
else
{
lean_object* v___x_1214_; 
lean_inc(v_value_1210_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_value_1210_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1215_, lean_object* v_x_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1215_, v_x_1216_);
lean_dec(v_x_1216_);
lean_dec(v_a_1215_);
return v_res_1217_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1218_; uint64_t v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(1723u);
v___x_1219_ = lean_uint64_of_nat(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_buckets_1222_; lean_object* v___x_1223_; uint64_t v___y_1225_; 
v_buckets_1222_ = lean_ctor_get(v_m_1220_, 1);
v___x_1223_ = lean_array_get_size(v_buckets_1222_);
if (lean_obj_tag(v_a_1221_) == 0)
{
uint64_t v___x_1239_; 
v___x_1239_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___closed__0);
v___y_1225_ = v___x_1239_;
goto v___jp_1224_;
}
else
{
uint64_t v_hash_1240_; 
v_hash_1240_ = lean_ctor_get_uint64(v_a_1221_, sizeof(void*)*2);
v___y_1225_ = v_hash_1240_;
goto v___jp_1224_;
}
v___jp_1224_:
{
uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v_fold_1228_; uint64_t v___x_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1226_ = 32ULL;
v___x_1227_ = lean_uint64_shift_right(v___y_1225_, v___x_1226_);
v_fold_1228_ = lean_uint64_xor(v___y_1225_, v___x_1227_);
v___x_1229_ = 16ULL;
v___x_1230_ = lean_uint64_shift_right(v_fold_1228_, v___x_1229_);
v___x_1231_ = lean_uint64_xor(v_fold_1228_, v___x_1230_);
v___x_1232_ = lean_uint64_to_usize(v___x_1231_);
v___x_1233_ = lean_usize_of_nat(v___x_1223_);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_sub(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_usize_land(v___x_1232_, v___x_1235_);
v___x_1237_ = lean_array_uget_borrowed(v_buckets_1222_, v___x_1236_);
v___x_1238_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1221_, v___x_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_m_1241_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___x_1247_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0));
v___x_1248_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1247_, v___x_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1251_, uint8_t v_isMeta_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v_env_1260_; lean_object* v___y_1262_; lean_object* v___x_1275_; 
v___x_1256_ = lean_st_ref_get(v___y_1254_);
v_env_1260_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1256_);
v___x_1275_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1260_, v_declName_1251_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref(v_env_1260_);
lean_dec(v_declName_1251_);
goto v___jp_1257_;
}
else
{
lean_object* v_val_1276_; lean_object* v___x_1277_; lean_object* v_modules_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_val_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l_Lean_Environment_header(v_env_1260_);
v_modules_1278_ = lean_ctor_get(v___x_1277_, 3);
lean_inc_ref(v_modules_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_array_get_size(v_modules_1278_);
v___x_1280_ = lean_nat_dec_lt(v_val_1276_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v_modules_1278_);
lean_dec(v_val_1276_);
lean_dec_ref(v_env_1260_);
lean_dec(v_declName_1251_);
goto v___jp_1257_;
}
else
{
lean_object* v___x_1281_; lean_object* v_env_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___y_1286_; 
v___x_1281_ = lean_st_ref_get(v___y_1254_);
v_env_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_ref(v_env_1282_);
lean_dec(v___x_1281_);
v___x_1283_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2);
v___x_1284_ = lean_array_fget(v_modules_1278_, v_val_1276_);
lean_dec(v_val_1276_);
lean_dec_ref(v_modules_1278_);
if (v_isMeta_1252_ == 0)
{
lean_dec_ref(v_env_1282_);
v___y_1286_ = v_isMeta_1252_;
goto v___jp_1285_;
}
else
{
uint8_t v___x_1297_; uint8_t v___x_1298_; 
lean_inc(v_declName_1251_);
v___x_1297_ = l_Lean_isMarkedMeta(v_env_1282_, v_declName_1251_);
v___x_1298_ = lean_bool_not(v___x_1297_);
v___y_1286_ = v___x_1298_;
goto v___jp_1285_;
}
v___jp_1285_:
{
lean_object* v_toImport_1287_; lean_object* v_module_1288_; lean_object* v___x_1289_; 
v_toImport_1287_ = lean_ctor_get(v___x_1284_, 0);
lean_inc_ref(v_toImport_1287_);
lean_dec(v___x_1284_);
v_module_1288_ = lean_ctor_get(v_toImport_1287_, 0);
lean_inc(v_module_1288_);
lean_dec_ref(v_toImport_1287_);
lean_inc(v_declName_1251_);
v___x_1289_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1288_, v___y_1286_, v_declName_1251_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref_known(v___x_1289_, 1);
v___x_1290_ = l_Lean_indirectModUseExt;
v___x_1291_ = lean_box(1);
v___x_1292_ = lean_box(0);
lean_inc_ref(v_env_1260_);
v___x_1293_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1283_, v___x_1290_, v_env_1260_, v___x_1291_, v___x_1292_);
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1293_, v_declName_1251_);
lean_dec(v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__3));
v___y_1262_ = v___x_1295_;
goto v___jp_1261_;
}
else
{
lean_object* v_val_1296_; 
v_val_1296_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___x_1294_, 1);
v___y_1262_ = v_val_1296_;
goto v___jp_1261_;
}
}
else
{
lean_dec_ref(v_env_1260_);
lean_dec(v_declName_1251_);
return v___x_1289_;
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; size_t v_sz_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v_sz_1264_ = lean_array_size(v___y_1262_);
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1260_, v_declName_1251_, v___y_1262_, v_sz_1264_, v___x_1265_, v___x_1263_, v___y_1253_, v___y_1254_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v_env_1260_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1274_);
v___x_1268_ = v___x_1266_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v___x_1266_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1263_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1263_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1299_, lean_object* v_isMeta_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v_isMeta_boxed_1304_; lean_object* v_res_1305_; 
v_isMeta_boxed_1304_ = lean_unbox(v_isMeta_1300_);
v_res_1305_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1299_, v_isMeta_boxed_1304_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
if (lean_obj_tag(v_as_x27_1306_) == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_b_1307_);
return v___x_1311_;
}
else
{
lean_object* v_head_1312_; lean_object* v_tail_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v_head_1312_ = lean_ctor_get(v_as_x27_1306_, 0);
v_tail_1313_ = lean_ctor_get(v_as_x27_1306_, 1);
v___x_1314_ = 1;
lean_inc(v_head_1312_);
v___x_1315_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1312_, v___x_1314_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref_known(v___x_1315_, 1);
v___x_1316_ = lean_box(0);
v_as_x27_1306_ = v_tail_1313_;
v_b_1307_ = v___x_1316_;
goto _start;
}
else
{
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1318_, v_b_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v_as_x27_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1324_, lean_object* v_opts_1325_, lean_object* v_currNamespace_1326_, lean_object* v_openDecls_1327_, lean_object* v_n_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = l_Lean_ResolveName_resolveGlobalName(v_env_1324_, v_opts_1325_, v_currNamespace_1326_, v_openDecls_1327_, v_n_1328_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1333_, lean_object* v_opts_1334_, lean_object* v_currNamespace_1335_, lean_object* v_openDecls_1336_, lean_object* v_n_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1333_, v_opts_1334_, v_currNamespace_1335_, v_openDecls_1336_, v_n_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_opts_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_Elab_Command_getRef___redArg(v___y_1343_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v_fileName_1348_; lean_object* v_fileMap_1349_; lean_object* v_currRecDepth_1350_; lean_object* v_cmdPos_1351_; lean_object* v_macroStack_1352_; lean_object* v_quotContext_x3f_1353_; lean_object* v_currMacroScope_1354_; lean_object* v_snap_x3f_1355_; lean_object* v_cancelTk_x3f_1356_; uint8_t v_suppressElabErrors_1357_; lean_object* v_ref_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v_fileName_1348_ = lean_ctor_get(v___y_1343_, 0);
v_fileMap_1349_ = lean_ctor_get(v___y_1343_, 1);
v_currRecDepth_1350_ = lean_ctor_get(v___y_1343_, 2);
v_cmdPos_1351_ = lean_ctor_get(v___y_1343_, 3);
v_macroStack_1352_ = lean_ctor_get(v___y_1343_, 4);
v_quotContext_x3f_1353_ = lean_ctor_get(v___y_1343_, 5);
v_currMacroScope_1354_ = lean_ctor_get(v___y_1343_, 6);
v_snap_x3f_1355_ = lean_ctor_get(v___y_1343_, 8);
v_cancelTk_x3f_1356_ = lean_ctor_get(v___y_1343_, 9);
v_suppressElabErrors_1357_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*10);
v_ref_1358_ = l_Lean_replaceRef(v_ref_1341_, v_a_1347_);
lean_dec(v_a_1347_);
lean_inc(v_cancelTk_x3f_1356_);
lean_inc(v_snap_x3f_1355_);
lean_inc(v_currMacroScope_1354_);
lean_inc(v_quotContext_x3f_1353_);
lean_inc(v_macroStack_1352_);
lean_inc(v_cmdPos_1351_);
lean_inc(v_currRecDepth_1350_);
lean_inc_ref(v_fileMap_1349_);
lean_inc_ref(v_fileName_1348_);
v___x_1359_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1359_, 0, v_fileName_1348_);
lean_ctor_set(v___x_1359_, 1, v_fileMap_1349_);
lean_ctor_set(v___x_1359_, 2, v_currRecDepth_1350_);
lean_ctor_set(v___x_1359_, 3, v_cmdPos_1351_);
lean_ctor_set(v___x_1359_, 4, v_macroStack_1352_);
lean_ctor_set(v___x_1359_, 5, v_quotContext_x3f_1353_);
lean_ctor_set(v___x_1359_, 6, v_currMacroScope_1354_);
lean_ctor_set(v___x_1359_, 7, v_ref_1358_);
lean_ctor_set(v___x_1359_, 8, v_snap_x3f_1355_);
lean_ctor_set(v___x_1359_, 9, v_cancelTk_x3f_1356_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*10, v_suppressElabErrors_1357_);
v___x_1360_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1342_, v___x_1359_, v___y_1344_);
lean_dec_ref_known(v___x_1359_, 10);
return v___x_1360_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_msg_1342_);
v_a_1361_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1346_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1346_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1369_, lean_object* v_msg_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1369_, v_msg_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v_ref_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1375_, lean_object* v_currNamespace_1376_, lean_object* v_openDecls_1377_, lean_object* v_n_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = l_Lean_ResolveName_resolveNamespace(v_env_1375_, v_currNamespace_1376_, v_openDecls_1377_, v_n_1378_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___y_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1383_, lean_object* v_currNamespace_1384_, lean_object* v_openDecls_1385_, lean_object* v_n_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1383_, v_currNamespace_1384_, v_openDecls_1385_, v_n_1386_, v___y_1387_, v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_currNamespace_1390_);
lean_ctor_set(v___x_1393_, 1, v___y_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1394_, v___y_1395_, v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1398_, lean_object* v___y_1399_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; 
v_a_1400_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_a_1400_);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_a_1400_);
lean_ctor_set(v___x_1401_, 1, v___y_1399_);
return v___x_1401_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_a_1402_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_a_1402_);
lean_ctor_set(v___x_1403_, 1, v___y_1399_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1404_, v___y_1405_);
lean_dec_ref(v_x_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1407_, lean_object* v_stx_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1407_, v_stx_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
if (lean_obj_tag(v_a_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_a_1413_ = lean_ctor_get(v___x_1411_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1422_);
v___x_1415_ = v___x_1411_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_box(0);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_a_1413_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1451_; 
v_val_1423_ = lean_ctor_get(v_a_1412_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_a_1412_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1425_ = v_a_1412_;
v_isShared_1426_ = v_isSharedCheck_1451_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_val_1423_);
lean_dec(v_a_1412_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1451_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_snd_1427_; 
v_snd_1427_ = lean_ctor_get(v_val_1423_, 1);
lean_inc(v_snd_1427_);
lean_dec(v_val_1423_);
if (lean_obj_tag(v_snd_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1425_);
v_a_1428_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1411_, 2);
v_a_1429_ = lean_ctor_get(v_snd_1427_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_snd_1427_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v_snd_1427_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v_snd_1427_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1434_, v_a_1428_);
lean_dec_ref(v___x_1434_);
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1450_; 
v_a_1438_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1411_, 2);
v_a_1439_ = lean_ctor_get(v_snd_1427_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_snd_1427_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1441_ = v_snd_1427_;
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_snd_1427_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_a_1439_);
v___x_1444_ = v___x_1425_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1444_);
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1446_, v_a_1438_);
lean_dec_ref(v___x_1446_);
return v___x_1447_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
v_a_1452_ = lean_ctor_get(v___x_1411_, 0);
v_a_1453_ = lean_ctor_get(v___x_1411_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1411_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_inc(v_a_1452_);
lean_dec(v___x_1411_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1452_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1461_, lean_object* v_stx_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1461_, v_stx_1462_, v___y_1463_, v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1465_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
if (lean_obj_tag(v_as_1474_) == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
else
{
lean_object* v_head_1480_; lean_object* v_tail_1481_; lean_object* v_fst_1482_; lean_object* v_snd_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_scopes_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_opts_1490_; uint8_t v_hasTrace_1491_; 
v_head_1480_ = lean_ctor_get(v_as_1474_, 0);
lean_inc(v_head_1480_);
v_tail_1481_ = lean_ctor_get(v_as_1474_, 1);
lean_inc(v_tail_1481_);
lean_dec_ref_known(v_as_1474_, 2);
v_fst_1482_ = lean_ctor_get(v_head_1480_, 0);
lean_inc(v_fst_1482_);
v_snd_1483_ = lean_ctor_get(v_head_1480_, 1);
lean_inc(v_snd_1483_);
lean_dec(v_head_1480_);
v___x_1484_ = l_Lean_inheritedTraceOptions;
v___x_1485_ = lean_st_ref_get(v___x_1484_);
v___x_1486_ = lean_st_ref_get(v___y_1476_);
v_scopes_1487_ = lean_ctor_get(v___x_1486_, 2);
lean_inc(v_scopes_1487_);
lean_dec(v___x_1486_);
v___x_1488_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1489_ = l_List_head_x21___redArg(v___x_1488_, v_scopes_1487_);
lean_dec(v_scopes_1487_);
v_opts_1490_ = lean_ctor_get(v___x_1489_, 1);
lean_inc_ref(v_opts_1490_);
lean_dec(v___x_1489_);
v_hasTrace_1491_ = lean_ctor_get_uint8(v_opts_1490_, sizeof(void*)*1);
if (v_hasTrace_1491_ == 0)
{
lean_dec_ref(v_opts_1490_);
lean_dec(v___x_1485_);
lean_dec(v_snd_1483_);
lean_dec(v_fst_1482_);
v_as_1474_ = v_tail_1481_;
goto _start;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
lean_inc(v_fst_1482_);
v___x_1494_ = l_Lean_Name_append(v___x_1493_, v_fst_1482_);
v___x_1495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1485_, v_opts_1490_, v___x_1494_);
lean_dec(v___x_1494_);
lean_dec_ref(v_opts_1490_);
lean_dec(v___x_1485_);
if (v___x_1495_ == 0)
{
lean_dec(v_snd_1483_);
lean_dec(v_fst_1482_);
v_as_1474_ = v_tail_1481_;
goto _start;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_snd_1483_);
v___x_1498_ = l_Lean_MessageData_ofFormat(v___x_1497_);
v___x_1499_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1482_, v___x_1498_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_dec_ref_known(v___x_1499_, 1);
v_as_1474_ = v_tail_1481_;
goto _start;
}
else
{
lean_dec(v_tail_1481_);
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v_env_1512_; lean_object* v___x_1513_; lean_object* v_scopes_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_opts_1517_; lean_object* v___x_1518_; 
v___x_1511_ = lean_st_ref_get(v___y_1509_);
v_env_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_env_1512_);
lean_dec(v___x_1511_);
v___x_1513_ = lean_st_ref_get(v___y_1509_);
v_scopes_1514_ = lean_ctor_get(v___x_1513_, 2);
lean_inc(v_scopes_1514_);
lean_dec(v___x_1513_);
v___x_1515_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1516_ = l_List_head_x21___redArg(v___x_1515_, v_scopes_1514_);
lean_dec(v_scopes_1514_);
v_opts_1517_ = lean_ctor_get(v___x_1516_, 1);
lean_inc_ref(v_opts_1517_);
lean_dec(v___x_1516_);
v___x_1518_ = l_Lean_Elab_Command_getScope___redArg(v___y_1509_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_currNamespace_1520_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v_currNamespace_1520_ = lean_ctor_get(v_a_1519_, 2);
lean_inc(v_currNamespace_1520_);
lean_dec(v_a_1519_);
v___x_1521_ = l_Lean_Elab_Command_getScope___redArg(v___y_1509_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_openDecls_1523_; lean_object* v___x_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_openDecls_1523_ = lean_ctor_get(v_a_1522_, 3);
lean_inc(v_openDecls_1523_);
lean_dec(v_a_1522_);
v___x_1524_ = l_Lean_Elab_Command_getRef___redArg(v___y_1508_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1508_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_currRecDepth_1528_; lean_object* v_quotContext_x3f_1529_; lean_object* v___f_1530_; lean_object* v___f_1531_; lean_object* v___f_1532_; lean_object* v___f_1533_; lean_object* v___f_1534_; lean_object* v_methods_1535_; lean_object* v_a_1537_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_currRecDepth_1528_ = lean_ctor_get(v___y_1508_, 2);
v_quotContext_x3f_1529_ = lean_ctor_get(v___y_1508_, 5);
lean_inc_ref_n(v_env_1512_, 3);
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1530_, 0, v_env_1512_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1531_, 0, v_env_1512_);
lean_inc_n(v_currNamespace_1520_, 2);
v___f_1532_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1532_, 0, v_currNamespace_1520_);
lean_inc(v_openDecls_1523_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1533_, 0, v_env_1512_);
lean_closure_set(v___f_1533_, 1, v_currNamespace_1520_);
lean_closure_set(v___f_1533_, 2, v_openDecls_1523_);
v___f_1534_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1534_, 0, v_env_1512_);
lean_closure_set(v___f_1534_, 1, v_opts_1517_);
lean_closure_set(v___f_1534_, 2, v_currNamespace_1520_);
lean_closure_set(v___f_1534_, 3, v_openDecls_1523_);
v_methods_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1535_, 0, v___f_1531_);
lean_ctor_set(v_methods_1535_, 1, v___f_1532_);
lean_ctor_set(v_methods_1535_, 2, v___f_1530_);
lean_ctor_set(v_methods_1535_, 3, v___f_1533_);
lean_ctor_set(v_methods_1535_, 4, v___f_1534_);
if (lean_obj_tag(v_quotContext_x3f_1529_) == 0)
{
lean_object* v___x_1609_; lean_object* v_a_1610_; 
v___x_1609_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1509_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v_a_1537_ = v_a_1610_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v_quotContext_x3f_1529_, 0);
lean_inc(v_val_1611_);
v_a_1537_ = v_val_1611_;
goto v___jp_1536_;
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v_maxRecDepth_1539_; lean_object* v___x_1540_; lean_object* v_nextMacroScope_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1538_ = lean_st_ref_get(v___y_1509_);
v_maxRecDepth_1539_ = lean_ctor_get(v___x_1538_, 5);
lean_inc(v_maxRecDepth_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = lean_st_ref_get(v___y_1509_);
v_nextMacroScope_1541_ = lean_ctor_get(v___x_1540_, 4);
lean_inc(v_nextMacroScope_1541_);
lean_dec(v___x_1540_);
lean_inc(v_currRecDepth_1528_);
v___x_1542_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1542_, 0, v_methods_1535_);
lean_ctor_set(v___x_1542_, 1, v_a_1537_);
lean_ctor_set(v___x_1542_, 2, v_a_1527_);
lean_ctor_set(v___x_1542_, 3, v_currRecDepth_1528_);
lean_ctor_set(v___x_1542_, 4, v_maxRecDepth_1539_);
lean_ctor_set(v___x_1542_, 5, v_a_1525_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1544_, 0, v_nextMacroScope_1541_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
lean_ctor_set(v___x_1544_, 2, v___x_1543_);
v___x_1545_ = lean_apply_2(v_x_1507_, v___x_1542_, v___x_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_a_1547_; lean_object* v_macroScope_1548_; lean_object* v_traceMsgs_1549_; lean_object* v_expandedMacroDecls_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_a_1546_);
v_a_1547_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1545_, 2);
v_macroScope_1548_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_macroScope_1548_);
v_traceMsgs_1549_ = lean_ctor_get(v_a_1546_, 1);
lean_inc(v_traceMsgs_1549_);
v_expandedMacroDecls_1550_ = lean_ctor_get(v_a_1546_, 2);
lean_inc(v_expandedMacroDecls_1550_);
lean_dec(v_a_1546_);
v___x_1551_ = lean_box(0);
v___x_1552_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1550_, v___x_1551_, v___y_1508_, v___y_1509_);
lean_dec(v_expandedMacroDecls_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; lean_object* v_env_1554_; lean_object* v_messages_1555_; lean_object* v_scopes_1556_; lean_object* v_usedQuotCtxts_1557_; lean_object* v_maxRecDepth_1558_; lean_object* v_ngen_1559_; lean_object* v_auxDeclNGen_1560_; lean_object* v_infoState_1561_; lean_object* v_traceState_1562_; lean_object* v_snapshotTasks_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref_known(v___x_1552_, 1);
v___x_1553_ = lean_st_ref_take(v___y_1509_);
v_env_1554_ = lean_ctor_get(v___x_1553_, 0);
v_messages_1555_ = lean_ctor_get(v___x_1553_, 1);
v_scopes_1556_ = lean_ctor_get(v___x_1553_, 2);
v_usedQuotCtxts_1557_ = lean_ctor_get(v___x_1553_, 3);
v_maxRecDepth_1558_ = lean_ctor_get(v___x_1553_, 5);
v_ngen_1559_ = lean_ctor_get(v___x_1553_, 6);
v_auxDeclNGen_1560_ = lean_ctor_get(v___x_1553_, 7);
v_infoState_1561_ = lean_ctor_get(v___x_1553_, 8);
v_traceState_1562_ = lean_ctor_get(v___x_1553_, 9);
v_snapshotTasks_1563_ = lean_ctor_get(v___x_1553_, 10);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v___x_1553_, 4);
lean_dec(v_unused_1590_);
v___x_1565_ = v___x_1553_;
v_isShared_1566_ = v_isSharedCheck_1589_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_snapshotTasks_1563_);
lean_inc(v_traceState_1562_);
lean_inc(v_infoState_1561_);
lean_inc(v_auxDeclNGen_1560_);
lean_inc(v_ngen_1559_);
lean_inc(v_maxRecDepth_1558_);
lean_inc(v_usedQuotCtxts_1557_);
lean_inc(v_scopes_1556_);
lean_inc(v_messages_1555_);
lean_inc(v_env_1554_);
lean_dec(v___x_1553_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1589_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 4, v_macroScope_1548_);
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_env_1554_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_messages_1555_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_scopes_1556_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_usedQuotCtxts_1557_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_macroScope_1548_);
lean_ctor_set(v_reuseFailAlloc_1588_, 5, v_maxRecDepth_1558_);
lean_ctor_set(v_reuseFailAlloc_1588_, 6, v_ngen_1559_);
lean_ctor_set(v_reuseFailAlloc_1588_, 7, v_auxDeclNGen_1560_);
lean_ctor_set(v_reuseFailAlloc_1588_, 8, v_infoState_1561_);
lean_ctor_set(v_reuseFailAlloc_1588_, 9, v_traceState_1562_);
lean_ctor_set(v_reuseFailAlloc_1588_, 10, v_snapshotTasks_1563_);
v___x_1568_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_st_ref_set(v___y_1509_, v___x_1568_);
v___x_1570_ = l_List_reverse___redArg(v_traceMsgs_1549_);
v___x_1571_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1570_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v___x_1571_, 0);
lean_dec(v_unused_1579_);
v___x_1573_ = v___x_1571_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v___x_1571_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_a_1547_);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1547_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1547_);
v_a_1580_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1571_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1571_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_traceMsgs_1549_);
lean_dec(v_macroScope_1548_);
lean_dec(v_a_1547_);
v_a_1591_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1552_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1552_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1545_, 2);
if (lean_obj_tag(v_a_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_a_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_a_1600_);
v_a_1601_ = lean_ctor_get(v_a_1599_, 1);
lean_inc_ref(v_a_1601_);
lean_dec_ref_known(v_a_1599_, 2);
v___x_1602_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1603_ = lean_string_dec_eq(v_a_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_a_1601_);
v___x_1605_ = l_Lean_MessageData_ofFormat(v___x_1604_);
v___x_1606_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1600_, v___x_1605_, v___y_1508_, v___y_1509_);
lean_dec(v_a_1600_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; 
lean_dec_ref(v_a_1601_);
v___x_1607_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1600_);
return v___x_1607_;
}
}
else
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1525_);
lean_dec(v_openDecls_1523_);
lean_dec(v_currNamespace_1520_);
lean_dec_ref(v_opts_1517_);
lean_dec_ref(v_env_1512_);
lean_dec_ref(v_x_1507_);
v_a_1612_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1526_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1526_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_openDecls_1523_);
lean_dec(v_currNamespace_1520_);
lean_dec_ref(v_opts_1517_);
lean_dec_ref(v_env_1512_);
lean_dec_ref(v_x_1507_);
v_a_1620_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1524_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1524_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_currNamespace_1520_);
lean_dec_ref(v_opts_1517_);
lean_dec_ref(v_env_1512_);
lean_dec_ref(v_x_1507_);
v_a_1628_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1521_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1521_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_opts_1517_);
lean_dec_ref(v_env_1512_);
lean_dec_ref(v_x_1507_);
v_a_1636_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1518_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1518_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1648_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1663_ = l_String_toRawSubstring_x27(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1687_ = lean_unsigned_to_nat(14u);
v___x_1688_ = lean_unsigned_to_nat(22u);
v___x_1689_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1690_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1691_ = l_mkPanicMessageWithDecl(v___x_1690_, v___x_1689_, v___x_1688_, v___x_1687_, v___x_1686_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1708_ = l_String_toRawSubstring_x27(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1721_ = l_Lean_mkAtom(v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1724_ = l_Lean_mkAtom(v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1725_, lean_object* v_id_1726_, lean_object* v_stx_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_pat_1732_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1727_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v_stx_1727_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1727_);
v___x_1738_ = l_Lean_Syntax_isOfKind(v_stx_1727_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v_a_1745_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v_a_1781_; uint8_t v___x_1812_; 
v___x_1739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1727_);
v___x_1812_ = l_Lean_Syntax_isOfKind(v_stx_1727_, v___x_1739_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1727_);
v___x_1814_ = l_Lean_Syntax_isOfKind(v_stx_1727_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1727_);
v___x_1816_ = l_Lean_Syntax_isOfKind(v_stx_1727_, v___x_1815_);
if (v___x_1816_ == 0)
{
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1819_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v_quotContext_x3f_1821_; lean_object* v___x_1822_; lean_object* v_a_1824_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v_quotContext_x3f_1821_ = lean_ctor_get(v_a_1728_, 5);
v___x_1822_ = l_Lean_SourceInfo_fromRef(v_a_1818_, v___x_1816_);
lean_dec(v_a_1818_);
if (lean_obj_tag(v_quotContext_x3f_1821_) == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v_a_1824_ = v_a_1856_;
goto v___jp_1823_;
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v___x_1822_);
lean_dec(v_a_1820_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_1857_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1855_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_val_1865_; 
v_val_1865_ = lean_ctor_get(v_quotContext_x3f_1821_, 0);
lean_inc(v_val_1865_);
v_a_1824_ = v_val_1865_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1825_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1826_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1827_ = l_Lean_addMacroScope(v_a_1824_, v___x_1826_, v_a_1820_);
v___x_1828_ = lean_box(0);
lean_inc_n(v___x_1822_, 3);
v___x_1829_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1822_);
lean_ctor_set(v___x_1829_, 1, v___x_1825_);
lean_ctor_set(v___x_1829_, 2, v___x_1827_);
lean_ctor_set(v___x_1829_, 3, v___x_1828_);
v___x_1830_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1822_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_1833_ = l_Lean_Syntax_node1(v___x_1822_, v___x_1832_, v_stx_1727_);
v___x_1834_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1846_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1846_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1846_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1822_);
v___x_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1822_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_Syntax_node4(v___x_1822_, v___x_1739_, v___x_1829_, v___x_1831_, v___x_1833_, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1842_);
v___x_1844_ = v___x_1837_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v___x_1833_);
lean_dec_ref_known(v___x_1831_, 2);
lean_dec_ref_known(v___x_1829_, 4);
lean_dec(v___x_1822_);
v_a_1847_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1834_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1834_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1818_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_1866_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1819_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1819_);
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
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_1874_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1817_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1817_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_val_1882_; lean_object* v___x_1883_; 
lean_dec(v_id_1726_);
v_val_1882_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_1882_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_1883_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_1882_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_pat_1732_ = v_a_1884_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_1893_);
lean_inc(v___x_1894_);
v___x_1895_ = l_Lean_Syntax_matchesNull(v___x_1894_, v___x_1893_);
if (v___x_1895_ == 0)
{
lean_dec(v___x_1894_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_quotContext_x3f_1900_; lean_object* v___x_1901_; lean_object* v_a_1903_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v_quotContext_x3f_1900_ = lean_ctor_get(v_a_1728_, 5);
v___x_1901_ = l_Lean_SourceInfo_fromRef(v_a_1897_, v___x_1895_);
lean_dec(v_a_1897_);
if (lean_obj_tag(v_quotContext_x3f_1900_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v_a_1903_ = v_a_1935_;
goto v___jp_1902_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v___x_1901_);
lean_dec(v_a_1899_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_1936_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1934_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1934_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_val_1944_; 
v_val_1944_ = lean_ctor_get(v_quotContext_x3f_1900_, 0);
lean_inc(v_val_1944_);
v_a_1903_ = v_val_1944_;
goto v___jp_1902_;
}
v___jp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1904_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1905_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1906_ = l_Lean_addMacroScope(v_a_1903_, v___x_1905_, v_a_1899_);
v___x_1907_ = lean_box(0);
lean_inc_n(v___x_1901_, 3);
v___x_1908_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1901_);
lean_ctor_set(v___x_1908_, 1, v___x_1904_);
lean_ctor_set(v___x_1908_, 2, v___x_1906_);
lean_ctor_set(v___x_1908_, 3, v___x_1907_);
v___x_1909_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1901_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_1912_ = l_Lean_Syntax_node1(v___x_1901_, v___x_1911_, v_stx_1727_);
v___x_1913_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1925_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1925_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1925_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1918_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1901_);
v___x_1919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1901_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_Syntax_node4(v___x_1901_, v___x_1739_, v___x_1908_, v___x_1910_, v___x_1912_, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v_a_1914_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1921_);
v___x_1923_ = v___x_1916_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v___x_1912_);
lean_dec_ref_known(v___x_1910_, 2);
lean_dec_ref_known(v___x_1908_, 4);
lean_dec(v___x_1901_);
v_a_1926_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1913_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1913_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_a_1897_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_1945_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1898_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1898_);
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
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_1953_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1896_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1896_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_val_1961_; lean_object* v___x_1962_; 
lean_dec(v_id_1726_);
v_val_1961_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_1961_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_1962_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_1961_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v_pat_1732_ = v_a_1963_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1972_ = lean_unsigned_to_nat(3u);
v___x_1973_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_1972_);
v___x_1974_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_1973_);
v___x_1975_ = l_Lean_Syntax_isOfKind(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_dec(v___x_1973_);
lean_dec(v___x_1894_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_quotContext_x3f_1980_; lean_object* v___x_1981_; lean_object* v_a_1983_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_quotContext_x3f_1980_ = lean_ctor_get(v_a_1728_, 5);
v___x_1981_ = l_Lean_SourceInfo_fromRef(v_a_1977_, v___x_1975_);
lean_dec(v_a_1977_);
if (lean_obj_tag(v_quotContext_x3f_1980_) == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v_a_1983_ = v_a_2015_;
goto v___jp_1982_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2016_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2014_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_val_2024_; 
v_val_2024_ = lean_ctor_get(v_quotContext_x3f_1980_, 0);
lean_inc(v_val_2024_);
v_a_1983_ = v_val_2024_;
goto v___jp_1982_;
}
v___jp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1984_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1985_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1986_ = l_Lean_addMacroScope(v_a_1983_, v___x_1985_, v_a_1979_);
v___x_1987_ = lean_box(0);
lean_inc_n(v___x_1981_, 3);
v___x_1988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1981_);
lean_ctor_set(v___x_1988_, 1, v___x_1984_);
lean_ctor_set(v___x_1988_, 2, v___x_1986_);
lean_ctor_set(v___x_1988_, 3, v___x_1987_);
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1981_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_1992_ = l_Lean_Syntax_node1(v___x_1981_, v___x_1991_, v_stx_1727_);
v___x_1993_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2005_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_1998_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_1981_);
v___x_1999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1981_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = l_Lean_Syntax_node4(v___x_1981_, v___x_1739_, v___x_1988_, v___x_1990_, v___x_1992_, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_a_1994_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2001_);
v___x_2003_ = v___x_1996_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v___x_1992_);
lean_dec_ref_known(v___x_1990_, 2);
lean_dec_ref_known(v___x_1988_, 4);
lean_dec(v___x_1981_);
v_a_2006_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1993_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1993_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1977_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2025_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1978_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1978_);
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
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2033_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1976_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1976_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_val_2041_; lean_object* v___x_2042_; 
lean_dec(v_id_1726_);
v_val_2041_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2042_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2041_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v_pat_1732_ = v_a_2043_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2052_; lean_object* v_stx_2053_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___x_2079_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v_stx_2053_ = l_Lean_Syntax_getArg(v___x_1894_, v___x_2052_);
lean_dec(v___x_1894_);
v___x_2079_ = lean_unsigned_to_nat(2u);
v___x_2131_ = lean_unsigned_to_nat(4u);
v___x_2132_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2131_);
v___x_2133_ = l_Lean_Syntax_isNone(v___x_2132_);
if (v___x_2133_ == 0)
{
uint8_t v___x_2134_; 
lean_inc(v___x_2132_);
v___x_2134_ = l_Lean_Syntax_matchesNull(v___x_2132_, v___x_2079_);
if (v___x_2134_ == 0)
{
lean_dec(v___x_2132_);
lean_dec(v_stx_2053_);
lean_dec(v___x_1973_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v_quotContext_x3f_2139_; lean_object* v___x_2140_; lean_object* v_a_2142_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_quotContext_x3f_2139_ = lean_ctor_get(v_a_1728_, 5);
v___x_2140_ = l_Lean_SourceInfo_fromRef(v_a_2136_, v___x_1814_);
lean_dec(v_a_2136_);
if (lean_obj_tag(v_quotContext_x3f_2139_) == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v_a_2142_ = v_a_2174_;
goto v___jp_2141_;
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v___x_2140_);
lean_dec(v_a_2138_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2175_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2173_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_val_2183_; 
v_val_2183_ = lean_ctor_get(v_quotContext_x3f_2139_, 0);
lean_inc(v_val_2183_);
v_a_2142_ = v_val_2183_;
goto v___jp_2141_;
}
v___jp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2143_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2145_ = l_Lean_addMacroScope(v_a_2142_, v___x_2144_, v_a_2138_);
v___x_2146_ = lean_box(0);
lean_inc_n(v___x_2140_, 3);
v___x_2147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2140_);
lean_ctor_set(v___x_2147_, 1, v___x_2143_);
lean_ctor_set(v___x_2147_, 2, v___x_2145_);
lean_ctor_set(v___x_2147_, 3, v___x_2146_);
v___x_2148_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2140_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2151_ = l_Lean_Syntax_node1(v___x_2140_, v___x_2150_, v_stx_1727_);
v___x_2152_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2164_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2164_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2164_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2157_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2140_);
v___x_2158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2140_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node4(v___x_2140_, v___x_1739_, v___x_2147_, v___x_2149_, v___x_2151_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v_a_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2160_);
v___x_2162_ = v___x_2155_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v___x_2151_);
lean_dec_ref_known(v___x_2149_, 2);
lean_dec_ref_known(v___x_2147_, 4);
lean_dec(v___x_2140_);
v_a_2165_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2152_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2152_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2136_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2184_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2137_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2137_);
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
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2192_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2135_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2135_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2201_; 
lean_dec(v_id_1726_);
v_val_2200_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2201_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2200_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v_pat_1732_ = v_a_2202_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = l_Lean_Syntax_getArg(v___x_2132_, v___x_1893_);
lean_dec(v___x_2132_);
v___x_2212_ = l_Lean_Syntax_matchesNull(v___x_2211_, v___x_1893_);
if (v___x_2212_ == 0)
{
lean_dec(v_stx_2053_);
lean_dec(v___x_1973_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v_quotContext_x3f_2217_; lean_object* v___x_2218_; lean_object* v_a_2220_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v_quotContext_x3f_2217_ = lean_ctor_get(v_a_1728_, 5);
v___x_2218_ = l_Lean_SourceInfo_fromRef(v_a_2214_, v___x_1814_);
lean_dec(v_a_2214_);
if (lean_obj_tag(v_quotContext_x3f_2217_) == 0)
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v_a_2220_ = v_a_2252_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v___x_2218_);
lean_dec(v_a_2216_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2253_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_val_2261_; 
v_val_2261_ = lean_ctor_get(v_quotContext_x3f_2217_, 0);
lean_inc(v_val_2261_);
v_a_2220_ = v_val_2261_;
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2221_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2222_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2223_ = l_Lean_addMacroScope(v_a_2220_, v___x_2222_, v_a_2216_);
v___x_2224_ = lean_box(0);
lean_inc_n(v___x_2218_, 3);
v___x_2225_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2218_);
lean_ctor_set(v___x_2225_, 1, v___x_2221_);
lean_ctor_set(v___x_2225_, 2, v___x_2223_);
lean_ctor_set(v___x_2225_, 3, v___x_2224_);
v___x_2226_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2218_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2229_ = l_Lean_Syntax_node1(v___x_2218_, v___x_2228_, v_stx_1727_);
v___x_2230_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2218_);
v___x_2236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2218_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_Syntax_node4(v___x_2218_, v___x_1739_, v___x_2225_, v___x_2227_, v___x_2229_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v_a_2231_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2238_);
v___x_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v___x_2229_);
lean_dec_ref_known(v___x_2227_, 2);
lean_dec_ref_known(v___x_2225_, 4);
lean_dec(v___x_2218_);
v_a_2243_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2230_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2230_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_a_2214_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2262_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2215_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2215_);
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
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2270_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2213_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2213_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_val_2278_; lean_object* v___x_2279_; 
lean_dec(v_id_1726_);
v_val_2278_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2279_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2278_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v_pat_1732_ = v_a_2280_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_stx_1727_);
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
}
else
{
v___y_2081_ = v_a_1728_;
v___y_2082_ = v_a_1729_;
goto v___jp_2080_;
}
}
}
else
{
lean_dec(v___x_2132_);
v___y_2081_ = v_a_1728_;
v___y_2082_ = v_a_1729_;
goto v___jp_2080_;
}
v___jp_2054_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2060_ = lean_string_append(v___y_2058_, v___x_2059_);
lean_inc(v___y_2057_);
v___x_2061_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2057_, v_stx_2053_, v_id_1726_, v___x_2060_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v_pat_1732_ = v_a_2062_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_stx_1727_);
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
v___jp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2075_ = l_Lean_Syntax_isStrLit_x3f(v___x_1973_);
lean_dec(v___x_1973_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2077_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2076_);
v___y_2055_ = v___y_2072_;
v___y_2056_ = v___y_2073_;
v___y_2057_ = v___x_2074_;
v___y_2058_ = v___x_2077_;
goto v___jp_2054_;
}
else
{
lean_object* v_val_2078_; 
v_val_2078_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___x_2075_, 1);
v___y_2055_ = v___y_2072_;
v___y_2056_ = v___y_2073_;
v___y_2057_ = v___x_2074_;
v___y_2058_ = v_val_2078_;
goto v___jp_2054_;
}
}
v___jp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = lean_unsigned_to_nat(5u);
v___x_2084_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2083_);
v___x_2085_ = l_Lean_Syntax_isNone(v___x_2084_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; 
v___x_2086_ = l_Lean_Syntax_matchesNull(v___x_2084_, v___x_2079_);
if (v___x_2086_ == 0)
{
lean_dec(v_stx_2053_);
lean_dec(v___x_1973_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Elab_Command_getRef___redArg(v___y_2081_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2081_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_quotContext_x3f_2091_; lean_object* v___x_2092_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v_quotContext_x3f_2091_ = lean_ctor_get(v___y_2081_, 5);
v___x_2092_ = l_Lean_SourceInfo_fromRef(v_a_2088_, v___x_1814_);
lean_dec(v_a_2088_);
if (lean_obj_tag(v_quotContext_x3f_2091_) == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2082_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___y_1741_ = v___x_2092_;
v___y_1742_ = v___y_2082_;
v___y_1743_ = v_a_2090_;
v___y_1744_ = v___y_2081_;
v_a_1745_ = v_a_2094_;
goto v___jp_1740_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v___x_2092_);
lean_dec(v_a_2090_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2095_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2093_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_val_2103_; 
v_val_2103_ = lean_ctor_get(v_quotContext_x3f_2091_, 0);
lean_inc(v_val_2103_);
v___y_1741_ = v___x_2092_;
v___y_1742_ = v___y_2082_;
v___y_1743_ = v_a_2090_;
v___y_1744_ = v___y_2081_;
v_a_1745_ = v_val_2103_;
goto v___jp_1740_;
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_a_2088_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2104_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2089_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2089_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2112_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2087_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2087_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2121_; 
lean_dec(v_id_1726_);
v_val_2120_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2121_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2120_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v_pat_1732_ = v_a_2122_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_dec(v_id_x3f_1725_);
v___y_2072_ = v___y_2081_;
v___y_2073_ = v___y_2082_;
goto v___jp_2071_;
}
}
else
{
lean_dec(v___x_2084_);
lean_dec(v_id_x3f_1725_);
v___y_2072_ = v___y_2081_;
v___y_2073_ = v___y_2082_;
goto v___jp_2071_;
}
}
}
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2289_);
lean_inc(v___x_2290_);
v___x_2291_ = l_Lean_Syntax_matchesNull(v___x_2290_, v___x_2289_);
if (v___x_2291_ == 0)
{
lean_dec(v___x_2290_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_quotContext_x3f_2296_; lean_object* v___x_2297_; lean_object* v_a_2299_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v_quotContext_x3f_2296_ = lean_ctor_get(v_a_1728_, 5);
v___x_2297_ = l_Lean_SourceInfo_fromRef(v_a_2293_, v___x_2291_);
lean_dec(v_a_2293_);
if (lean_obj_tag(v_quotContext_x3f_2296_) == 0)
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v_a_2299_ = v_a_2331_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v___x_2297_);
lean_dec(v_a_2295_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2332_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2330_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_val_2340_; 
v_val_2340_ = lean_ctor_get(v_quotContext_x3f_2296_, 0);
lean_inc(v_val_2340_);
v_a_2299_ = v_val_2340_;
goto v___jp_2298_;
}
v___jp_2298_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2300_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2302_ = l_Lean_addMacroScope(v_a_2299_, v___x_2301_, v_a_2295_);
v___x_2303_ = lean_box(0);
lean_inc_n(v___x_2297_, 3);
v___x_2304_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2297_);
lean_ctor_set(v___x_2304_, 1, v___x_2300_);
lean_ctor_set(v___x_2304_, 2, v___x_2302_);
lean_ctor_set(v___x_2304_, 3, v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2297_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2308_ = l_Lean_Syntax_node1(v___x_2297_, v___x_2307_, v_stx_1727_);
v___x_2309_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2321_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2297_);
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2297_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_node4(v___x_2297_, v___x_1739_, v___x_2304_, v___x_2306_, v___x_2308_, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_a_2310_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2317_);
v___x_2319_ = v___x_2312_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v___x_2308_);
lean_dec_ref_known(v___x_2306_, 2);
lean_dec_ref_known(v___x_2304_, 4);
lean_dec(v___x_2297_);
v_a_2322_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2309_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2309_);
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
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2293_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2341_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2294_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2294_);
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
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2349_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2292_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2292_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_val_2357_; lean_object* v___x_2358_; 
lean_dec(v_id_1726_);
v_val_2357_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2357_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2358_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2357_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v_pat_1732_ = v_a_2359_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2368_ = lean_unsigned_to_nat(3u);
v___x_2369_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2368_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2369_);
v___x_2371_ = l_Lean_Syntax_isOfKind(v___x_2369_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec(v___x_2369_);
lean_dec(v___x_2290_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v_quotContext_x3f_2376_; lean_object* v___x_2377_; lean_object* v_a_2379_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v_quotContext_x3f_2376_ = lean_ctor_get(v_a_1728_, 5);
v___x_2377_ = l_Lean_SourceInfo_fromRef(v_a_2373_, v___x_2371_);
lean_dec(v_a_2373_);
if (lean_obj_tag(v_quotContext_x3f_2376_) == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v_a_2379_ = v_a_2411_;
goto v___jp_2378_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v___x_2377_);
lean_dec(v_a_2375_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2412_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2410_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_val_2420_; 
v_val_2420_ = lean_ctor_get(v_quotContext_x3f_2376_, 0);
lean_inc(v_val_2420_);
v_a_2379_ = v_val_2420_;
goto v___jp_2378_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2380_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2382_ = l_Lean_addMacroScope(v_a_2379_, v___x_2381_, v_a_2375_);
v___x_2383_ = lean_box(0);
lean_inc_n(v___x_2377_, 3);
v___x_2384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2377_);
lean_ctor_set(v___x_2384_, 1, v___x_2380_);
lean_ctor_set(v___x_2384_, 2, v___x_2382_);
lean_ctor_set(v___x_2384_, 3, v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2377_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2388_ = l_Lean_Syntax_node1(v___x_2377_, v___x_2387_, v_stx_1727_);
v___x_2389_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2401_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2377_);
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2377_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_Syntax_node4(v___x_2377_, v___x_1739_, v___x_2384_, v___x_2386_, v___x_2388_, v___x_2395_);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v_a_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2397_);
v___x_2399_ = v___x_2392_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v___x_2388_);
lean_dec_ref_known(v___x_2386_, 2);
lean_dec_ref_known(v___x_2384_, 4);
lean_dec(v___x_2377_);
v_a_2402_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2389_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2389_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_a_2373_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2421_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2374_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2374_);
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
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2429_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2372_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2372_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_val_2437_; lean_object* v___x_2438_; 
lean_dec(v_id_1726_);
v_val_2437_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2438_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2437_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v_pat_1732_ = v_a_2439_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2448_; lean_object* v_stx_2449_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___x_2475_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
v_stx_2449_ = l_Lean_Syntax_getArg(v___x_2290_, v___x_2448_);
lean_dec(v___x_2290_);
v___x_2475_ = lean_unsigned_to_nat(2u);
v___x_2527_ = lean_unsigned_to_nat(4u);
v___x_2528_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2527_);
v___x_2529_ = l_Lean_Syntax_isNone(v___x_2528_);
if (v___x_2529_ == 0)
{
uint8_t v___x_2530_; 
lean_inc(v___x_2528_);
v___x_2530_ = l_Lean_Syntax_matchesNull(v___x_2528_, v___x_2475_);
if (v___x_2530_ == 0)
{
lean_dec(v___x_2528_);
lean_dec(v_stx_2449_);
lean_dec(v___x_2369_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v_quotContext_x3f_2535_; lean_object* v___x_2536_; lean_object* v_a_2538_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v_quotContext_x3f_2535_ = lean_ctor_get(v_a_1728_, 5);
v___x_2536_ = l_Lean_SourceInfo_fromRef(v_a_2532_, v___x_1812_);
lean_dec(v_a_2532_);
if (lean_obj_tag(v_quotContext_x3f_2535_) == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v_a_2538_ = v_a_2570_;
goto v___jp_2537_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v___x_2536_);
lean_dec(v_a_2534_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2571_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2569_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2569_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v_val_2579_; 
v_val_2579_ = lean_ctor_get(v_quotContext_x3f_2535_, 0);
lean_inc(v_val_2579_);
v_a_2538_ = v_val_2579_;
goto v___jp_2537_;
}
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2539_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2540_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2541_ = l_Lean_addMacroScope(v_a_2538_, v___x_2540_, v_a_2534_);
v___x_2542_ = lean_box(0);
lean_inc_n(v___x_2536_, 3);
v___x_2543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2536_);
lean_ctor_set(v___x_2543_, 1, v___x_2539_);
lean_ctor_set(v___x_2543_, 2, v___x_2541_);
lean_ctor_set(v___x_2543_, 3, v___x_2542_);
v___x_2544_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2536_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2547_ = l_Lean_Syntax_node1(v___x_2536_, v___x_2546_, v_stx_1727_);
v___x_2548_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2560_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2560_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2560_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2553_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2536_);
v___x_2554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2536_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node4(v___x_2536_, v___x_1739_, v___x_2543_, v___x_2545_, v___x_2547_, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v_a_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2556_);
v___x_2558_ = v___x_2551_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v___x_2547_);
lean_dec_ref_known(v___x_2545_, 2);
lean_dec_ref_known(v___x_2543_, 4);
lean_dec(v___x_2536_);
v_a_2561_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2548_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2548_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_a_2532_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2580_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2533_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2533_);
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
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2588_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2531_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2531_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_val_2596_; lean_object* v___x_2597_; 
lean_dec(v_id_1726_);
v_val_2596_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2597_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2596_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v_pat_1732_ = v_a_2598_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = l_Lean_Syntax_getArg(v___x_2528_, v___x_2289_);
lean_dec(v___x_2528_);
v___x_2608_ = l_Lean_Syntax_matchesNull(v___x_2607_, v___x_2289_);
if (v___x_2608_ == 0)
{
lean_dec(v_stx_2449_);
lean_dec(v___x_2369_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v_quotContext_x3f_2613_; lean_object* v___x_2614_; lean_object* v_a_2616_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_quotContext_x3f_2613_ = lean_ctor_get(v_a_1728_, 5);
v___x_2614_ = l_Lean_SourceInfo_fromRef(v_a_2610_, v___x_1812_);
lean_dec(v_a_2610_);
if (lean_obj_tag(v_quotContext_x3f_2613_) == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v_a_2616_ = v_a_2648_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v___x_2614_);
lean_dec(v_a_2612_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2649_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2647_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2647_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_val_2657_; 
v_val_2657_ = lean_ctor_get(v_quotContext_x3f_2613_, 0);
lean_inc(v_val_2657_);
v_a_2616_ = v_val_2657_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2617_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2618_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2619_ = l_Lean_addMacroScope(v_a_2616_, v___x_2618_, v_a_2612_);
v___x_2620_ = lean_box(0);
lean_inc_n(v___x_2614_, 3);
v___x_2621_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2614_);
lean_ctor_set(v___x_2621_, 1, v___x_2617_);
lean_ctor_set(v___x_2621_, 2, v___x_2619_);
lean_ctor_set(v___x_2621_, 3, v___x_2620_);
v___x_2622_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2614_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2625_ = l_Lean_Syntax_node1(v___x_2614_, v___x_2624_, v_stx_1727_);
v___x_2626_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2638_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2638_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2638_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2614_);
v___x_2632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2614_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = l_Lean_Syntax_node4(v___x_2614_, v___x_1739_, v___x_2621_, v___x_2623_, v___x_2625_, v___x_2632_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
lean_ctor_set(v___x_2634_, 1, v_a_2627_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2634_);
v___x_2636_ = v___x_2629_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v___x_2625_);
lean_dec_ref_known(v___x_2623_, 2);
lean_dec_ref_known(v___x_2621_, 4);
lean_dec(v___x_2614_);
v_a_2639_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2626_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2626_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_a_2610_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2658_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2611_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2611_);
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
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2666_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2609_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2609_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_val_2674_; lean_object* v___x_2675_; 
lean_dec(v_id_1726_);
v_val_2674_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2674_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2675_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2674_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v_pat_1732_ = v_a_2676_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_stx_1727_);
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
}
else
{
v___y_2477_ = v_a_1728_;
v___y_2478_ = v_a_1729_;
goto v___jp_2476_;
}
}
}
else
{
lean_dec(v___x_2528_);
v___y_2477_ = v_a_1728_;
v___y_2478_ = v_a_1729_;
goto v___jp_2476_;
}
v___jp_2450_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2456_ = lean_string_append(v___y_2454_, v___x_2455_);
lean_inc(v___y_2453_);
v___x_2457_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2453_, v_stx_2449_, v_id_1726_, v___x_2456_, v___y_2452_, v___y_2451_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v_pat_1732_ = v_a_2458_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_stx_1727_);
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
v___jp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2471_ = l_Lean_Syntax_isStrLit_x3f(v___x_2369_);
lean_dec(v___x_2369_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2473_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2472_);
v___y_2451_ = v___y_2469_;
v___y_2452_ = v___y_2468_;
v___y_2453_ = v___x_2470_;
v___y_2454_ = v___x_2473_;
goto v___jp_2450_;
}
else
{
lean_object* v_val_2474_; 
v_val_2474_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2471_, 1);
v___y_2451_ = v___y_2469_;
v___y_2452_ = v___y_2468_;
v___y_2453_ = v___x_2470_;
v___y_2454_ = v_val_2474_;
goto v___jp_2450_;
}
}
v___jp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2479_ = lean_unsigned_to_nat(5u);
v___x_2480_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2479_);
v___x_2481_ = l_Lean_Syntax_isNone(v___x_2480_);
if (v___x_2481_ == 0)
{
uint8_t v___x_2482_; 
v___x_2482_ = l_Lean_Syntax_matchesNull(v___x_2480_, v___x_2475_);
if (v___x_2482_ == 0)
{
lean_dec(v_stx_2449_);
lean_dec(v___x_2369_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Elab_Command_getRef___redArg(v___y_2477_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2477_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v_quotContext_x3f_2487_; lean_object* v___x_2488_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v_quotContext_x3f_2487_ = lean_ctor_get(v___y_2477_, 5);
v___x_2488_ = l_Lean_SourceInfo_fromRef(v_a_2484_, v___x_1812_);
lean_dec(v_a_2484_);
if (lean_obj_tag(v_quotContext_x3f_2487_) == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2478_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___y_1777_ = v___y_2478_;
v___y_1778_ = v___y_2477_;
v___y_1779_ = v___x_2488_;
v___y_1780_ = v_a_2486_;
v_a_1781_ = v_a_2490_;
goto v___jp_1776_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v___x_2488_);
lean_dec(v_a_2486_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2489_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2489_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v_val_2499_; 
v_val_2499_ = lean_ctor_get(v_quotContext_x3f_2487_, 0);
lean_inc(v_val_2499_);
v___y_1777_ = v___y_2478_;
v___y_1778_ = v___y_2477_;
v___y_1779_ = v___x_2488_;
v___y_1780_ = v_a_2486_;
v_a_1781_ = v_val_2499_;
goto v___jp_1776_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_a_2484_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2500_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2485_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2485_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2508_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2483_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2483_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2517_; 
lean_dec(v_id_1726_);
v_val_2516_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2516_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2517_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2516_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v_pat_1732_ = v_a_2518_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_dec(v_id_x3f_1725_);
v___y_2468_ = v___y_2477_;
v___y_2469_ = v___y_2478_;
goto v___jp_2467_;
}
}
else
{
lean_dec(v___x_2480_);
lean_dec(v_id_x3f_1725_);
v___y_2468_ = v___y_2477_;
v___y_2469_ = v___y_2478_;
goto v___jp_2467_;
}
}
}
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2688_ = l_Lean_Syntax_matchesIdent(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2690_ = l_Lean_Syntax_matchesIdent(v___x_2686_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2691_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2692_ = l_Lean_Syntax_matchesIdent(v___x_2686_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2694_ = l_Lean_Syntax_matchesIdent(v___x_2686_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2696_ = l_Lean_Syntax_matchesIdent(v___x_2686_, v___x_2695_);
lean_dec(v___x_2686_);
if (v___x_2696_ == 0)
{
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v_quotContext_x3f_2701_; lean_object* v___x_2702_; lean_object* v_a_2704_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v_quotContext_x3f_2701_ = lean_ctor_get(v_a_1728_, 5);
v___x_2702_ = l_Lean_SourceInfo_fromRef(v_a_2698_, v___x_2696_);
lean_dec(v_a_2698_);
if (lean_obj_tag(v_quotContext_x3f_2701_) == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v_a_2704_ = v_a_2736_;
goto v___jp_2703_;
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___x_2702_);
lean_dec(v_a_2700_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2737_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2735_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2735_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v_val_2745_; 
v_val_2745_ = lean_ctor_get(v_quotContext_x3f_2701_, 0);
lean_inc(v_val_2745_);
v_a_2704_ = v_val_2745_;
goto v___jp_2703_;
}
v___jp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2706_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2707_ = l_Lean_addMacroScope(v_a_2704_, v___x_2706_, v_a_2700_);
v___x_2708_ = lean_box(0);
lean_inc_n(v___x_2702_, 3);
v___x_2709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2702_);
lean_ctor_set(v___x_2709_, 1, v___x_2705_);
lean_ctor_set(v___x_2709_, 2, v___x_2707_);
lean_ctor_set(v___x_2709_, 3, v___x_2708_);
v___x_2710_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2702_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2713_ = l_Lean_Syntax_node1(v___x_2702_, v___x_2712_, v_stx_1727_);
v___x_2714_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2726_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2702_);
v___x_2720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2702_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_Syntax_node4(v___x_2702_, v___x_1739_, v___x_2709_, v___x_2711_, v___x_2713_, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_a_2715_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2722_);
v___x_2724_ = v___x_2717_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v___x_2713_);
lean_dec_ref_known(v___x_2711_, 2);
lean_dec_ref_known(v___x_2709_, 4);
lean_dec(v___x_2702_);
v_a_2727_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2714_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2714_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2698_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2746_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2699_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2699_);
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
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2754_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2697_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2697_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_val_2762_; lean_object* v___x_2763_; 
lean_dec(v_id_1726_);
v_val_2762_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2762_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2763_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2762_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v_pat_1732_ = v_a_2764_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2773_ = lean_unsigned_to_nat(1u);
v___x_2774_ = lean_unsigned_to_nat(2u);
v___x_2775_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2774_);
lean_inc(v___x_2775_);
v___x_2776_ = l_Lean_Syntax_matchesNull(v___x_2775_, v___x_2773_);
if (v___x_2776_ == 0)
{
lean_dec(v___x_2775_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v_quotContext_x3f_2781_; lean_object* v___x_2782_; lean_object* v_a_2784_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v_quotContext_x3f_2781_ = lean_ctor_get(v_a_1728_, 5);
v___x_2782_ = l_Lean_SourceInfo_fromRef(v_a_2778_, v___x_2776_);
lean_dec(v_a_2778_);
if (lean_obj_tag(v_quotContext_x3f_2781_) == 0)
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v_a_2784_ = v_a_2816_;
goto v___jp_2783_;
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v___x_2782_);
lean_dec(v_a_2780_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2817_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2815_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2815_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_val_2825_; 
v_val_2825_ = lean_ctor_get(v_quotContext_x3f_2781_, 0);
lean_inc(v_val_2825_);
v_a_2784_ = v_val_2825_;
goto v___jp_2783_;
}
v___jp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2785_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2786_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2787_ = l_Lean_addMacroScope(v_a_2784_, v___x_2786_, v_a_2780_);
v___x_2788_ = lean_box(0);
lean_inc_n(v___x_2782_, 3);
v___x_2789_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2782_);
lean_ctor_set(v___x_2789_, 1, v___x_2785_);
lean_ctor_set(v___x_2789_, 2, v___x_2787_);
lean_ctor_set(v___x_2789_, 3, v___x_2788_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2782_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2793_ = l_Lean_Syntax_node1(v___x_2782_, v___x_2792_, v_stx_1727_);
v___x_2794_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2806_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2806_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2806_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2782_);
v___x_2800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2782_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_Syntax_node4(v___x_2782_, v___x_1739_, v___x_2789_, v___x_2791_, v___x_2793_, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v_a_2795_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2802_);
v___x_2804_ = v___x_2797_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v___x_2793_);
lean_dec_ref_known(v___x_2791_, 2);
lean_dec_ref_known(v___x_2789_, 4);
lean_dec(v___x_2782_);
v_a_2807_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2794_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2794_);
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
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2778_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2826_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2779_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2779_);
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
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2834_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2777_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2777_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_val_2842_; lean_object* v___x_2843_; 
lean_dec(v_id_1726_);
v_val_2842_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2843_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2842_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v_pat_1732_ = v_a_2844_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v_stx_2853_; lean_object* v___x_2854_; 
lean_dec(v_stx_1727_);
v_stx_2853_ = l_Lean_Syntax_getArg(v___x_2775_, v___x_2685_);
lean_dec(v___x_2775_);
v___x_2854_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1725_, v_id_1726_, v_stx_2853_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_fst_2856_; lean_object* v_snd_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2917_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v_fst_2856_ = lean_ctor_get(v_a_2855_, 0);
v_snd_2857_ = lean_ctor_get(v_a_2855_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2859_ = v_a_2855_;
v_isShared_2860_ = v_isSharedCheck_2917_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_snd_2857_);
lean_inc(v_fst_2856_);
lean_dec(v_a_2855_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2917_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2900_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2900_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2900_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_quotContext_x3f_2868_; lean_object* v___x_2869_; lean_object* v_a_2871_; 
v_quotContext_x3f_2868_ = lean_ctor_get(v_a_1728_, 5);
v___x_2869_ = l_Lean_SourceInfo_fromRef(v_a_2862_, v___x_2694_);
lean_dec(v_a_2862_);
if (lean_obj_tag(v_quotContext_x3f_2868_) == 0)
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v_a_2871_ = v_a_2890_;
goto v___jp_2870_;
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v___x_2869_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2859_);
lean_dec(v_snd_2857_);
lean_dec(v_fst_2856_);
v_a_2891_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2889_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_val_2899_; 
v_val_2899_ = lean_ctor_get(v_quotContext_x3f_2868_, 0);
lean_inc(v_val_2899_);
v_a_2871_ = v_val_2899_;
goto v___jp_2870_;
}
v___jp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2872_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_2873_ = l_Lean_addMacroScope(v_a_2871_, v___x_2695_, v_a_2864_);
v___x_2874_ = lean_box(0);
lean_inc_n(v___x_2869_, 4);
v___x_2875_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2869_);
lean_ctor_set(v___x_2875_, 1, v___x_2872_);
lean_ctor_set(v___x_2875_, 2, v___x_2873_);
lean_ctor_set(v___x_2875_, 3, v___x_2874_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2869_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_2879_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2878_, v_fst_2856_);
v___x_2880_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2869_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = l_Lean_Syntax_node4(v___x_2869_, v___x_1739_, v___x_2875_, v___x_2877_, v___x_2879_, v___x_2881_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2882_);
v___x_2884_ = v___x_2859_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_snd_2857_);
v___x_2884_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2886_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2884_);
v___x_2886_ = v___x_2866_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_a_2862_);
lean_del_object(v___x_2859_);
lean_dec(v_snd_2857_);
lean_dec(v_fst_2856_);
v_a_2901_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2863_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2863_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_del_object(v___x_2859_);
lean_dec(v_snd_2857_);
lean_dec(v_fst_2856_);
v_a_2909_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2861_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2861_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
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
return v___x_2854_;
}
}
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
lean_dec(v___x_2686_);
v___x_2918_ = lean_unsigned_to_nat(1u);
v___x_2919_ = lean_unsigned_to_nat(2u);
v___x_2920_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_2919_);
lean_inc(v___x_2920_);
v___x_2921_ = l_Lean_Syntax_matchesNull(v___x_2920_, v___x_2918_);
if (v___x_2921_ == 0)
{
lean_dec(v___x_2920_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v_quotContext_x3f_2926_; lean_object* v___x_2927_; lean_object* v_a_2929_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v_quotContext_x3f_2926_ = lean_ctor_get(v_a_1728_, 5);
v___x_2927_ = l_Lean_SourceInfo_fromRef(v_a_2923_, v___x_2921_);
lean_dec(v_a_2923_);
if (lean_obj_tag(v_quotContext_x3f_2926_) == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v_a_2929_ = v_a_2961_;
goto v___jp_2928_;
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v___x_2927_);
lean_dec(v_a_2925_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2962_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2960_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2960_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_val_2970_; 
v_val_2970_ = lean_ctor_get(v_quotContext_x3f_2926_, 0);
lean_inc(v_val_2970_);
v_a_2929_ = v_val_2970_;
goto v___jp_2928_;
}
v___jp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2930_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2931_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2932_ = l_Lean_addMacroScope(v_a_2929_, v___x_2931_, v_a_2925_);
v___x_2933_ = lean_box(0);
lean_inc_n(v___x_2927_, 3);
v___x_2934_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2927_);
lean_ctor_set(v___x_2934_, 1, v___x_2930_);
lean_ctor_set(v___x_2934_, 2, v___x_2932_);
lean_ctor_set(v___x_2934_, 3, v___x_2933_);
v___x_2935_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2927_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_2938_ = l_Lean_Syntax_node1(v___x_2927_, v___x_2937_, v_stx_1727_);
v___x_2939_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2951_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2951_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2951_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2927_);
v___x_2945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2927_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l_Lean_Syntax_node4(v___x_2927_, v___x_1739_, v___x_2934_, v___x_2936_, v___x_2938_, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v_a_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2947_);
v___x_2949_ = v___x_2942_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v___x_2938_);
lean_dec_ref_known(v___x_2936_, 2);
lean_dec_ref_known(v___x_2934_, 4);
lean_dec(v___x_2927_);
v_a_2952_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2939_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2939_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_a_2923_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2971_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2924_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2924_);
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
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_2979_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2922_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2922_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v_val_2987_; lean_object* v___x_2988_; 
lean_dec(v_id_1726_);
v_val_2987_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_2987_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_2988_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_2987_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v_pat_1732_ = v_a_2989_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2998_ = l_Lean_Syntax_getArg(v___x_2920_, v___x_2685_);
lean_dec(v___x_2920_);
v___x_2999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_2998_);
v___x_3000_ = l_Lean_Syntax_isOfKind(v___x_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec(v___x_2998_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v_quotContext_x3f_3005_; lean_object* v___x_3006_; lean_object* v_a_3008_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_quotContext_x3f_3005_ = lean_ctor_get(v_a_1728_, 5);
v___x_3006_ = l_Lean_SourceInfo_fromRef(v_a_3002_, v___x_3000_);
lean_dec(v_a_3002_);
if (lean_obj_tag(v_quotContext_x3f_3005_) == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v_a_3008_ = v_a_3040_;
goto v___jp_3007_;
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v___x_3006_);
lean_dec(v_a_3004_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3041_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3039_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3039_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
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
else
{
lean_object* v_val_3049_; 
v_val_3049_ = lean_ctor_get(v_quotContext_x3f_3005_, 0);
lean_inc(v_val_3049_);
v_a_3008_ = v_val_3049_;
goto v___jp_3007_;
}
v___jp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3009_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3010_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3011_ = l_Lean_addMacroScope(v_a_3008_, v___x_3010_, v_a_3004_);
v___x_3012_ = lean_box(0);
lean_inc_n(v___x_3006_, 3);
v___x_3013_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3006_);
lean_ctor_set(v___x_3013_, 1, v___x_3009_);
lean_ctor_set(v___x_3013_, 2, v___x_3011_);
lean_ctor_set(v___x_3013_, 3, v___x_3012_);
v___x_3014_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3006_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3017_ = l_Lean_Syntax_node1(v___x_3006_, v___x_3016_, v_stx_1727_);
v___x_3018_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3030_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3030_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3030_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3006_);
v___x_3024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3006_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Lean_Syntax_node4(v___x_3006_, v___x_1739_, v___x_3013_, v___x_3015_, v___x_3017_, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v_a_3019_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3026_);
v___x_3028_ = v___x_3021_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v___x_3017_);
lean_dec_ref_known(v___x_3015_, 2);
lean_dec_ref_known(v___x_3013_, 4);
lean_dec(v___x_3006_);
v_a_3031_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3018_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3018_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_3002_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3050_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3003_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3003_);
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
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3058_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3001_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3001_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_val_3066_; lean_object* v___x_3067_; 
lean_dec(v_id_1726_);
v_val_3066_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3066_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3067_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3066_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v_pat_1732_ = v_a_3068_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = l_Lean_Syntax_getArg(v___x_2998_, v___x_2685_);
v___x_3078_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3079_ = l_Lean_Syntax_matchesIdent(v___x_3077_, v___x_3078_);
lean_dec(v___x_3077_);
if (v___x_3079_ == 0)
{
lean_dec(v___x_2998_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_quotContext_x3f_3084_; lean_object* v___x_3085_; lean_object* v_a_3087_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v_quotContext_x3f_3084_ = lean_ctor_get(v_a_1728_, 5);
v___x_3085_ = l_Lean_SourceInfo_fromRef(v_a_3081_, v___x_3079_);
lean_dec(v_a_3081_);
if (lean_obj_tag(v_quotContext_x3f_3084_) == 0)
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v_a_3087_ = v_a_3119_;
goto v___jp_3086_;
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v___x_3085_);
lean_dec(v_a_3083_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3120_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3118_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3118_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_val_3128_; 
v_val_3128_ = lean_ctor_get(v_quotContext_x3f_3084_, 0);
lean_inc(v_val_3128_);
v_a_3087_ = v_val_3128_;
goto v___jp_3086_;
}
v___jp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3088_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3089_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3090_ = l_Lean_addMacroScope(v_a_3087_, v___x_3089_, v_a_3083_);
v___x_3091_ = lean_box(0);
lean_inc_n(v___x_3085_, 3);
v___x_3092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3085_);
lean_ctor_set(v___x_3092_, 1, v___x_3088_);
lean_ctor_set(v___x_3092_, 2, v___x_3090_);
lean_ctor_set(v___x_3092_, 3, v___x_3091_);
v___x_3093_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3085_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3096_ = l_Lean_Syntax_node1(v___x_3085_, v___x_3095_, v_stx_1727_);
v___x_3097_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3109_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3109_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3109_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3085_);
v___x_3103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3085_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = l_Lean_Syntax_node4(v___x_3085_, v___x_1739_, v___x_3092_, v___x_3094_, v___x_3096_, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v_a_3098_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3105_);
v___x_3107_ = v___x_3100_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v___x_3096_);
lean_dec_ref_known(v___x_3094_, 2);
lean_dec_ref_known(v___x_3092_, 4);
lean_dec(v___x_3085_);
v_a_3110_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3097_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3097_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3081_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3129_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3082_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3082_);
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
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3137_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3080_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3080_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3146_; 
lean_dec(v_id_1726_);
v_val_3145_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3145_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3146_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3145_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v_pat_1732_ = v_a_3147_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = l_Lean_Syntax_getArg(v___x_2998_, v___x_2918_);
lean_dec(v___x_2998_);
v___x_3157_ = l_Lean_Syntax_matchesNull(v___x_3156_, v___x_2685_);
if (v___x_3157_ == 0)
{
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v_quotContext_x3f_3162_; lean_object* v___x_3163_; lean_object* v_a_3165_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v_quotContext_x3f_3162_ = lean_ctor_get(v_a_1728_, 5);
v___x_3163_ = l_Lean_SourceInfo_fromRef(v_a_3159_, v___x_3157_);
lean_dec(v_a_3159_);
if (lean_obj_tag(v_quotContext_x3f_3162_) == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v_a_3165_ = v_a_3197_;
goto v___jp_3164_;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v___x_3163_);
lean_dec(v_a_3161_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3198_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3196_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3196_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_val_3206_; 
v_val_3206_ = lean_ctor_get(v_quotContext_x3f_3162_, 0);
lean_inc(v_val_3206_);
v_a_3165_ = v_val_3206_;
goto v___jp_3164_;
}
v___jp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3166_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3167_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3168_ = l_Lean_addMacroScope(v_a_3165_, v___x_3167_, v_a_3161_);
v___x_3169_ = lean_box(0);
lean_inc_n(v___x_3163_, 3);
v___x_3170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3163_);
lean_ctor_set(v___x_3170_, 1, v___x_3166_);
lean_ctor_set(v___x_3170_, 2, v___x_3168_);
lean_ctor_set(v___x_3170_, 3, v___x_3169_);
v___x_3171_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3163_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3174_ = l_Lean_Syntax_node1(v___x_3163_, v___x_3173_, v_stx_1727_);
v___x_3175_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3187_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3187_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3187_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3163_);
v___x_3181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3163_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Lean_Syntax_node4(v___x_3163_, v___x_1739_, v___x_3170_, v___x_3172_, v___x_3174_, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
lean_ctor_set(v___x_3183_, 1, v_a_3176_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3183_);
v___x_3185_ = v___x_3178_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v___x_3174_);
lean_dec_ref_known(v___x_3172_, 2);
lean_dec_ref_known(v___x_3170_, 4);
lean_dec(v___x_3163_);
v_a_3188_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3175_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3175_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_a_3159_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3207_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3160_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3160_);
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
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3215_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3158_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3158_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_val_3223_; lean_object* v___x_3224_; 
lean_dec(v_id_1726_);
v_val_3223_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3223_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3224_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3223_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_pat_1732_ = v_a_3225_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec(v_id_x3f_1725_);
v___x_3234_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3235_ = lean_box(0);
v___x_3236_ = l_Lean_Syntax_mkAntiquotNode(v___x_3234_, v_id_1726_, v___x_2685_, v___x_3235_, v___x_2692_);
v_pat_1732_ = v___x_3236_;
goto v___jp_1731_;
}
}
}
}
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
lean_dec(v___x_2686_);
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_unsigned_to_nat(2u);
v___x_3239_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_3238_);
lean_inc(v___x_3239_);
v___x_3240_ = l_Lean_Syntax_matchesNull(v___x_3239_, v___x_3237_);
if (v___x_3240_ == 0)
{
lean_dec(v___x_3239_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v_quotContext_x3f_3245_; lean_object* v___x_3246_; lean_object* v_a_3248_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
v_quotContext_x3f_3245_ = lean_ctor_get(v_a_1728_, 5);
v___x_3246_ = l_Lean_SourceInfo_fromRef(v_a_3242_, v___x_3240_);
lean_dec(v_a_3242_);
if (lean_obj_tag(v_quotContext_x3f_3245_) == 0)
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v_a_3248_ = v_a_3280_;
goto v___jp_3247_;
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v___x_3246_);
lean_dec(v_a_3244_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3281_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3279_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_object* v_val_3289_; 
v_val_3289_ = lean_ctor_get(v_quotContext_x3f_3245_, 0);
lean_inc(v_val_3289_);
v_a_3248_ = v_val_3289_;
goto v___jp_3247_;
}
v___jp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3249_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3250_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3251_ = l_Lean_addMacroScope(v_a_3248_, v___x_3250_, v_a_3244_);
v___x_3252_ = lean_box(0);
lean_inc_n(v___x_3246_, 3);
v___x_3253_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3246_);
lean_ctor_set(v___x_3253_, 1, v___x_3249_);
lean_ctor_set(v___x_3253_, 2, v___x_3251_);
lean_ctor_set(v___x_3253_, 3, v___x_3252_);
v___x_3254_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3246_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3257_ = l_Lean_Syntax_node1(v___x_3246_, v___x_3256_, v_stx_1727_);
v___x_3258_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3270_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3270_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3270_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3263_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3246_);
v___x_3264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3246_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_Syntax_node4(v___x_3246_, v___x_1739_, v___x_3253_, v___x_3255_, v___x_3257_, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set(v___x_3266_, 1, v_a_3259_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3266_);
v___x_3268_ = v___x_3261_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v___x_3257_);
lean_dec_ref_known(v___x_3255_, 2);
lean_dec_ref_known(v___x_3253_, 4);
lean_dec(v___x_3246_);
v_a_3271_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3258_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3258_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_a_3242_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3290_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3243_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3243_);
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
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3298_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3241_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3241_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v_val_3306_; lean_object* v___x_3307_; 
lean_dec(v_id_1726_);
v_val_3306_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3307_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3306_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v_pat_1732_ = v_a_3308_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v_stx_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec(v_id_x3f_1725_);
v_stx_3317_ = l_Lean_Syntax_getArg(v___x_3239_, v___x_2685_);
lean_dec(v___x_3239_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3319_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2689_, v_stx_3317_, v_id_1726_, v___x_3318_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v_pat_1732_ = v_a_3320_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_stx_1727_);
v_a_3321_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3319_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
lean_dec(v___x_2686_);
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = lean_unsigned_to_nat(2u);
v___x_3331_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_3330_);
lean_inc(v___x_3331_);
v___x_3332_ = l_Lean_Syntax_matchesNull(v___x_3331_, v___x_3329_);
if (v___x_3332_ == 0)
{
lean_dec(v___x_3331_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3335_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3335_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_quotContext_x3f_3337_; lean_object* v___x_3338_; lean_object* v_a_3340_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v_quotContext_x3f_3337_ = lean_ctor_get(v_a_1728_, 5);
v___x_3338_ = l_Lean_SourceInfo_fromRef(v_a_3334_, v___x_3332_);
lean_dec(v_a_3334_);
if (lean_obj_tag(v_quotContext_x3f_3337_) == 0)
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v_a_3340_ = v_a_3372_;
goto v___jp_3339_;
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v___x_3338_);
lean_dec(v_a_3336_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_val_3381_; 
v_val_3381_ = lean_ctor_get(v_quotContext_x3f_3337_, 0);
lean_inc(v_val_3381_);
v_a_3340_ = v_val_3381_;
goto v___jp_3339_;
}
v___jp_3339_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3341_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3342_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3343_ = l_Lean_addMacroScope(v_a_3340_, v___x_3342_, v_a_3336_);
v___x_3344_ = lean_box(0);
lean_inc_n(v___x_3338_, 3);
v___x_3345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3338_);
lean_ctor_set(v___x_3345_, 1, v___x_3341_);
lean_ctor_set(v___x_3345_, 2, v___x_3343_);
lean_ctor_set(v___x_3345_, 3, v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3338_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3349_ = l_Lean_Syntax_node1(v___x_3338_, v___x_3348_, v_stx_1727_);
v___x_3350_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3362_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3362_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3362_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3338_);
v___x_3356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3338_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_Syntax_node4(v___x_3338_, v___x_1739_, v___x_3345_, v___x_3347_, v___x_3349_, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v_a_3351_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3358_);
v___x_3360_ = v___x_3353_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v___x_3349_);
lean_dec_ref_known(v___x_3347_, 2);
lean_dec_ref_known(v___x_3345_, 4);
lean_dec(v___x_3338_);
v_a_3363_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3350_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3350_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v_a_3334_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3382_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3335_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3335_);
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
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3390_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3333_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3333_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_val_3398_; lean_object* v___x_3399_; 
lean_dec(v_id_1726_);
v_val_3398_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3399_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3398_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v_pat_1732_ = v_a_3400_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v_stx_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec(v_id_x3f_1725_);
v_stx_3409_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_2685_);
lean_dec(v___x_3331_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3411_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2689_, v_stx_3409_, v_id_1726_, v___x_3410_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v_pat_1732_ = v_a_3412_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_stx_1727_);
v_a_3413_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3411_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3411_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
lean_dec(v___x_2686_);
v___x_3421_ = lean_unsigned_to_nat(1u);
v___x_3422_ = lean_unsigned_to_nat(2u);
v___x_3423_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_3422_);
lean_inc(v___x_3423_);
v___x_3424_ = l_Lean_Syntax_matchesNull(v___x_3423_, v___x_3421_);
if (v___x_3424_ == 0)
{
lean_dec(v___x_3423_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v_quotContext_x3f_3429_; lean_object* v___x_3430_; lean_object* v_a_3432_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v_quotContext_x3f_3429_ = lean_ctor_get(v_a_1728_, 5);
v___x_3430_ = l_Lean_SourceInfo_fromRef(v_a_3426_, v___x_3424_);
lean_dec(v_a_3426_);
if (lean_obj_tag(v_quotContext_x3f_3429_) == 0)
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v_a_3432_ = v_a_3464_;
goto v___jp_3431_;
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v___x_3430_);
lean_dec(v_a_3428_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3465_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3463_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_val_3473_; 
v_val_3473_ = lean_ctor_get(v_quotContext_x3f_3429_, 0);
lean_inc(v_val_3473_);
v_a_3432_ = v_val_3473_;
goto v___jp_3431_;
}
v___jp_3431_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3433_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3434_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3435_ = l_Lean_addMacroScope(v_a_3432_, v___x_3434_, v_a_3428_);
v___x_3436_ = lean_box(0);
lean_inc_n(v___x_3430_, 3);
v___x_3437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3430_);
lean_ctor_set(v___x_3437_, 1, v___x_3433_);
lean_ctor_set(v___x_3437_, 2, v___x_3435_);
lean_ctor_set(v___x_3437_, 3, v___x_3436_);
v___x_3438_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3430_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3441_ = l_Lean_Syntax_node1(v___x_3430_, v___x_3440_, v_stx_1727_);
v___x_3442_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3454_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3454_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3454_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3447_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3430_);
v___x_3448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3430_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = l_Lean_Syntax_node4(v___x_3430_, v___x_1739_, v___x_3437_, v___x_3439_, v___x_3441_, v___x_3448_);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v_a_3443_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3450_);
v___x_3452_ = v___x_3445_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v___x_3441_);
lean_dec_ref_known(v___x_3439_, 2);
lean_dec_ref_known(v___x_3437_, 4);
lean_dec(v___x_3430_);
v_a_3455_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3442_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3442_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v_a_3426_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3474_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3427_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3427_);
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
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3482_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3425_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3425_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v_val_3490_; lean_object* v___x_3491_; 
lean_dec(v_id_1726_);
v_val_3490_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3490_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3491_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3490_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v_pat_1732_ = v_a_3492_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v_stx_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_dec(v_id_x3f_1725_);
v_stx_3501_ = l_Lean_Syntax_getArg(v___x_3423_, v___x_2685_);
lean_dec(v___x_3423_);
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3503_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2687_, v_stx_3501_, v_id_1726_, v___x_3502_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v_pat_1732_ = v_a_3504_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_stx_1727_);
v_a_3505_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3503_);
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
}
}
v___jp_1740_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1746_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1747_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1748_ = l_Lean_addMacroScope(v_a_1745_, v___x_1747_, v___y_1743_);
v___x_1749_ = lean_box(0);
lean_inc_n(v___y_1741_, 3);
v___x_1750_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1750_, 0, v___y_1741_);
lean_ctor_set(v___x_1750_, 1, v___x_1746_);
lean_ctor_set(v___x_1750_, 2, v___x_1748_);
lean_ctor_set(v___x_1750_, 3, v___x_1749_);
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___y_1741_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_1754_ = l_Lean_Syntax_node1(v___y_1741_, v___x_1753_, v_stx_1727_);
v___x_1755_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v___y_1744_, v___y_1742_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1767_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1767_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1767_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1741_);
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1741_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Syntax_node4(v___y_1741_, v___x_1739_, v___x_1750_, v___x_1752_, v___x_1754_, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1763_);
v___x_1765_ = v___x_1758_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v___x_1754_);
lean_dec_ref_known(v___x_1752_, 2);
lean_dec_ref_known(v___x_1750_, 4);
lean_dec(v___y_1741_);
v_a_1768_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1755_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1755_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
v___jp_1776_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1782_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1783_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1784_ = l_Lean_addMacroScope(v_a_1781_, v___x_1783_, v___y_1780_);
v___x_1785_ = lean_box(0);
lean_inc_n(v___y_1779_, 3);
v___x_1786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1779_);
lean_ctor_set(v___x_1786_, 1, v___x_1782_);
lean_ctor_set(v___x_1786_, 2, v___x_1784_);
lean_ctor_set(v___x_1786_, 3, v___x_1785_);
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___y_1779_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_1790_ = l_Lean_Syntax_node1(v___y_1779_, v___x_1789_, v_stx_1727_);
v___x_1791_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v___y_1778_, v___y_1777_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1803_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1803_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1803_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1779_);
v___x_1797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___y_1779_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node4(v___y_1779_, v___x_1739_, v___x_1786_, v___x_1788_, v___x_1790_, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_a_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1799_);
v___x_1801_ = v___x_1794_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v___x_1790_);
lean_dec_ref_known(v___x_1788_, 2);
lean_dec_ref_known(v___x_1786_, 4);
lean_dec(v___y_1779_);
v_a_1804_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1791_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1791_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_3513_);
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3514_);
v___x_3516_ = l_Lean_Syntax_isOfKind(v___x_3514_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_dec(v___x_3514_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v_quotContext_x3f_3521_; lean_object* v___x_3522_; lean_object* v_a_3524_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v_quotContext_x3f_3521_ = lean_ctor_get(v_a_1728_, 5);
v___x_3522_ = l_Lean_SourceInfo_fromRef(v_a_3518_, v___x_3516_);
lean_dec(v_a_3518_);
if (lean_obj_tag(v_quotContext_x3f_3521_) == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v_a_3524_ = v_a_3557_;
goto v___jp_3523_;
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec(v___x_3522_);
lean_dec(v_a_3520_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3558_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3556_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3556_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_object* v_val_3566_; 
v_val_3566_ = lean_ctor_get(v_quotContext_x3f_3521_, 0);
lean_inc(v_val_3566_);
v_a_3524_ = v_val_3566_;
goto v___jp_3523_;
}
v___jp_3523_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3525_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3527_ = l_Lean_addMacroScope(v_a_3524_, v___x_3526_, v_a_3520_);
v___x_3528_ = lean_box(0);
lean_inc_n(v___x_3522_, 3);
v___x_3529_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3522_);
lean_ctor_set(v___x_3529_, 1, v___x_3525_);
lean_ctor_set(v___x_3529_, 2, v___x_3527_);
lean_ctor_set(v___x_3529_, 3, v___x_3528_);
v___x_3530_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3522_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3533_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3532_, v_stx_1727_);
v___x_3534_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3547_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3547_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3547_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3539_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3522_);
v___x_3540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3522_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3542_ = l_Lean_Syntax_node4(v___x_3522_, v___x_3541_, v___x_3529_, v___x_3531_, v___x_3533_, v___x_3540_);
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
lean_ctor_set(v___x_3543_, 1, v_a_3535_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3543_);
v___x_3545_ = v___x_3537_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v___x_3533_);
lean_dec_ref_known(v___x_3531_, 2);
lean_dec_ref_known(v___x_3529_, 4);
lean_dec(v___x_3522_);
v_a_3548_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3534_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3534_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_a_3518_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3567_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3519_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3519_);
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
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3575_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3517_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3517_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v_val_3583_; lean_object* v___x_3584_; 
lean_dec(v_id_1726_);
v_val_3583_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3583_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3584_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3583_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3584_, 1);
v_pat_1732_ = v_a_3585_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec(v_id_x3f_1725_);
v___x_3594_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3594_, 0, v___x_3514_);
v___x_3595_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3594_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3595_, 1);
v___x_3597_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3598_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3599_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3600_ = lean_unsigned_to_nat(4u);
v___x_3601_ = lean_mk_empty_array_with_capacity(v___x_3600_);
v___x_3602_ = lean_array_push(v___x_3601_, v_a_3596_);
v___x_3603_ = lean_array_push(v___x_3602_, v___x_3598_);
v___x_3604_ = lean_array_push(v___x_3603_, v___x_3599_);
v___x_3605_ = lean_array_push(v___x_3604_, v_id_1726_);
v___x_3606_ = lean_box(2);
v___x_3607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v___x_3597_);
lean_ctor_set(v___x_3607_, 2, v___x_3605_);
v_pat_1732_ = v___x_3607_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3608_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3595_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3595_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = l_Lean_Syntax_getArg(v_stx_1727_, v___x_3616_);
v___x_3618_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3617_);
v___x_3619_ = l_Lean_Syntax_isOfKind(v___x_3617_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_dec(v___x_3617_);
if (lean_obj_tag(v_id_x3f_1725_) == 0)
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_Elab_Command_getRef___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3622_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1728_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v_quotContext_x3f_3624_; lean_object* v___x_3625_; lean_object* v_a_3627_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v_quotContext_x3f_3624_ = lean_ctor_get(v_a_1728_, 5);
v___x_3625_ = l_Lean_SourceInfo_fromRef(v_a_3621_, v___x_3619_);
lean_dec(v_a_3621_);
if (lean_obj_tag(v_quotContext_x3f_3624_) == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1729_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v_a_3627_ = v_a_3660_;
goto v___jp_3626_;
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v___x_3625_);
lean_dec(v_a_3623_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3661_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3659_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_val_3669_; 
v_val_3669_ = lean_ctor_get(v_quotContext_x3f_3624_, 0);
lean_inc(v_val_3669_);
v_a_3627_ = v_val_3669_;
goto v___jp_3626_;
}
v___jp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3628_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3629_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3630_ = l_Lean_addMacroScope(v_a_3627_, v___x_3629_, v_a_3623_);
v___x_3631_ = lean_box(0);
lean_inc_n(v___x_3625_, 3);
v___x_3632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3625_);
lean_ctor_set(v___x_3632_, 1, v___x_3628_);
lean_ctor_set(v___x_3632_, 2, v___x_3630_);
lean_ctor_set(v___x_3632_, 3, v___x_3631_);
v___x_3633_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3625_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1727_);
v___x_3636_ = l_Lean_Syntax_node1(v___x_3625_, v___x_3635_, v_stx_1727_);
v___x_3637_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_id_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3650_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3650_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3650_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3642_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3625_);
v___x_3643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3625_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3645_ = l_Lean_Syntax_node4(v___x_3625_, v___x_3644_, v___x_3632_, v___x_3634_, v___x_3636_, v___x_3643_);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v_a_3638_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3646_);
v___x_3648_ = v___x_3640_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec(v___x_3636_);
lean_dec_ref_known(v___x_3634_, 2);
lean_dec_ref_known(v___x_3632_, 4);
lean_dec(v___x_3625_);
v_a_3651_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3637_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3637_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_a_3621_);
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3670_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3622_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3622_);
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
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3678_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3620_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3620_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_val_3686_; lean_object* v___x_3687_; 
lean_dec(v_id_1726_);
v_val_3686_ = lean_ctor_get(v_id_x3f_1725_, 0);
lean_inc(v_val_3686_);
lean_dec_ref_known(v_id_x3f_1725_, 1);
lean_inc(v_stx_1727_);
v___x_3687_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1727_, v_val_3686_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v_pat_1732_ = v_a_3688_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_stx_1727_);
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
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_dec(v_id_x3f_1725_);
v___x_3697_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3697_, 0, v___x_3617_);
v___x_3698_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3697_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3701_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3702_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3703_ = lean_unsigned_to_nat(4u);
v___x_3704_ = lean_mk_empty_array_with_capacity(v___x_3703_);
v___x_3705_ = lean_array_push(v___x_3704_, v_a_3699_);
v___x_3706_ = lean_array_push(v___x_3705_, v___x_3701_);
v___x_3707_ = lean_array_push(v___x_3706_, v___x_3702_);
v___x_3708_ = lean_array_push(v___x_3707_, v_id_1726_);
v___x_3709_ = lean_box(2);
v___x_3710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___x_3700_);
lean_ctor_set(v___x_3710_, 2, v___x_3708_);
v_pat_1732_ = v___x_3710_;
goto v___jp_1731_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_stx_1727_);
lean_dec(v_id_1726_);
v_a_3711_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3698_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3698_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
v___jp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_stx_1727_);
lean_ctor_set(v___x_1733_, 1, v_pat_1732_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3719_, lean_object* v_id_3720_, lean_object* v_stx_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3719_, v_id_3720_, v_stx_3721_, v_a_3722_, v_a_3723_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3726_, lean_object* v_x_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3727_, v___y_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_x_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3731_, v_x_3732_, v___y_3733_, v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec_ref(v_x_3732_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3736_, lean_object* v_ref_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3737_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3742_, lean_object* v_ref_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3742_, v_ref_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3758_, lean_object* v_x_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3759_, v___y_3760_, v___y_3761_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3764_, lean_object* v_x_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3764_, v_x_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3770_, lean_object* v_as_x27_3771_, lean_object* v_b_3772_, lean_object* v_a_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3771_, v_b_3772_, v___y_3774_, v___y_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3778_, lean_object* v_as_x27_3779_, lean_object* v_b_3780_, lean_object* v_a_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3778_, v_as_x27_3779_, v_b_3780_, v_a_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v_as_x27_3779_);
lean_dec(v_as_3778_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3786_, lean_object* v_ref_3787_, lean_object* v_msg_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3787_, v_msg_3788_, v___y_3789_, v___y_3790_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3793_, lean_object* v_ref_3794_, lean_object* v_msg_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3793_, v_ref_3794_, v_msg_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_ref_3794_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3800_, lean_object* v_m_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3801_, v_a_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3804_, lean_object* v_m_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3804_, v_m_3805_, v_a_3806_);
lean_dec(v_a_3806_);
lean_dec_ref(v_m_3805_);
return v_res_3807_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_){
_start:
{
uint8_t v___x_3811_; 
v___x_3811_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3809_, v_x_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_){
_start:
{
uint8_t v_res_3815_; lean_object* v_r_3816_; 
v_res_3815_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_3812_, v_x_3813_, v_x_3814_);
lean_dec_ref(v_x_3814_);
lean_dec_ref(v_x_3813_);
v_r_3816_ = lean_box(v_res_3815_);
return v_r_3816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3817_, lean_object* v_a_3818_, lean_object* v_x_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_3818_, v_x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3821_, lean_object* v_a_3822_, lean_object* v_x_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_3821_, v_a_3822_, v_x_3823_);
lean_dec(v_x_3823_);
lean_dec(v_a_3822_);
return v_res_3824_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3825_, lean_object* v_x_3826_, size_t v_x_3827_, lean_object* v_x_3828_){
_start:
{
uint8_t v___x_3829_; 
v___x_3829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_3826_, v_x_3827_, v_x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3830_, lean_object* v_x_3831_, lean_object* v_x_3832_, lean_object* v_x_3833_){
_start:
{
size_t v_x_90422__boxed_3834_; uint8_t v_res_3835_; lean_object* v_r_3836_; 
v_x_90422__boxed_3834_ = lean_unbox_usize(v_x_3832_);
lean_dec(v_x_3832_);
v_res_3835_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_3830_, v_x_3831_, v_x_90422__boxed_3834_, v_x_3833_);
lean_dec_ref(v_x_3833_);
lean_dec_ref(v_x_3831_);
v_r_3836_ = lean_box(v_res_3835_);
return v_r_3836_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_3837_, lean_object* v_keys_3838_, lean_object* v_vals_3839_, lean_object* v_heq_3840_, lean_object* v_i_3841_, lean_object* v_k_3842_){
_start:
{
uint8_t v___x_3843_; 
v___x_3843_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_3838_, v_i_3841_, v_k_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3844_, lean_object* v_keys_3845_, lean_object* v_vals_3846_, lean_object* v_heq_3847_, lean_object* v_i_3848_, lean_object* v_k_3849_){
_start:
{
uint8_t v_res_3850_; lean_object* v_r_3851_; 
v_res_3850_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_3844_, v_keys_3845_, v_vals_3846_, v_heq_3847_, v_i_3848_, v_k_3849_);
lean_dec_ref(v_k_3849_);
lean_dec_ref(v_vals_3846_);
lean_dec_ref(v_keys_3845_);
v_r_3851_ = lean_box(v_res_3850_);
return v_r_3851_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_k_3858_){
_start:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; uint8_t v___x_3861_; 
v___x_3859_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_3860_ = lean_name_eq(v_k_3858_, v___x_3859_);
v___x_3861_ = lean_bool_not(v___x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_k_3862_){
_start:
{
uint8_t v_res_3863_; lean_object* v_r_3864_; 
v_res_3863_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_3862_);
lean_dec(v_k_3862_);
v_r_3864_ = lean_box(v_res_3863_);
return v_r_3864_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_3875_ = l_String_toRawSubstring_x27(v___x_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___f_3882_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_3883_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_3883_, 0, v_stx_3878_);
lean_closure_set(v___x_3883_, 1, v___f_3882_);
v___x_3884_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3883_, v_a_3879_, v_a_3880_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc_n(v_a_3885_, 2);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3886_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_3887_ = l_Lean_Syntax_isOfKind(v_a_3885_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_a_3885_);
v___x_3888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = l_Lean_Syntax_getArg(v_a_3885_, v___x_3897_);
v___x_3899_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3898_);
v___x_3900_ = l_Lean_Syntax_matchesNull(v___x_3898_, v___x_3899_);
if (v___x_3900_ == 0)
{
uint8_t v___x_3901_; 
v___x_3901_ = l_Lean_Syntax_matchesNull(v___x_3898_, v___x_3897_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v_a_3885_);
v___x_3902_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Elab_Command_getRef___redArg(v_a_3879_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3879_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v_quotContext_x3f_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v_a_3920_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v_quotContext_x3f_3915_ = lean_ctor_get(v_a_3879_, 5);
v___x_3916_ = lean_unsigned_to_nat(1u);
v___x_3917_ = l_Lean_Syntax_getArg(v_a_3885_, v___x_3916_);
lean_dec(v_a_3885_);
v___x_3918_ = l_Lean_SourceInfo_fromRef(v_a_3912_, v___x_3900_);
lean_dec(v_a_3912_);
if (lean_obj_tag(v_quotContext_x3f_3915_) == 0)
{
lean_object* v___x_3928_; lean_object* v_a_3929_; 
v___x_3928_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_3880_);
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref(v___x_3928_);
v_a_3920_ = v_a_3929_;
goto v___jp_3919_;
}
else
{
lean_object* v_val_3930_; 
v_val_3930_ = lean_ctor_get(v_quotContext_x3f_3915_, 0);
lean_inc(v_val_3930_);
v_a_3920_ = v_val_3930_;
goto v___jp_3919_;
}
v___jp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3921_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_3922_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_3923_ = l_Lean_addMacroScope(v_a_3920_, v___x_3922_, v_a_3914_);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3918_);
lean_ctor_set(v___x_3925_, 1, v___x_3921_);
lean_ctor_set(v___x_3925_, 2, v___x_3923_);
lean_ctor_set(v___x_3925_, 3, v___x_3924_);
v___x_3926_ = lean_box(0);
v___x_3927_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3926_, v___x_3925_, v___x_3917_, v_a_3879_, v_a_3880_);
return v___x_3927_;
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_a_3912_);
lean_dec(v_a_3885_);
v_a_3931_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3913_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3913_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec(v_a_3885_);
v_a_3939_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3911_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3911_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3947_ = l_Lean_Syntax_getArg(v___x_3898_, v___x_3897_);
lean_dec(v___x_3898_);
v___x_3948_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_3947_);
v___x_3949_ = l_Lean_Syntax_isOfKind(v___x_3947_, v___x_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v___x_3947_);
lean_dec(v_a_3885_);
v___x_3950_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3950_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3950_);
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
else
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = l_Lean_Syntax_getArg(v_a_3885_, v___x_3959_);
lean_dec(v_a_3885_);
lean_inc(v___x_3947_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3947_);
v___x_3962_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3961_, v___x_3947_, v___x_3960_, v_a_3879_, v_a_3880_);
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_a_3963_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3884_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3884_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Elab_Command_expandMacroArg(v_stx_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
return v_res_3975_;
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
