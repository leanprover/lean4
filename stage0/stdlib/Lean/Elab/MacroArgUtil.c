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
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Parser_getParserAliasInfo(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_33_, 1);
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
uint8_t v___x_15276__boxed_65_; uint8_t v___x_15277__boxed_66_; lean_object* v_res_67_; 
v___x_15276__boxed_65_ = lean_unbox(v___x_59_);
v___x_15277__boxed_66_ = lean_unbox(v___x_60_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_57_, v___x_58_, v___x_15276__boxed_65_, v___x_15277__boxed_66_, v_x_61_, v___y_62_, v___y_63_);
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
lean_object* v_id_127_; 
v_id_127_ = l_Lean_Syntax_getArg(v___x_107_, v___x_105_);
if (v___x_124_ == 0)
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_127_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_id_127_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_id_127_);
goto v___jp_108_;
}
else
{
goto v___jp_128_;
}
}
else
{
goto v___jp_128_;
}
v___jp_128_:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = lean_unsigned_to_nat(2u);
v___x_130_ = l_Lean_Syntax_getArg(v___x_107_, v___x_129_);
v___x_131_ = l_Lean_Syntax_matchesNull(v___x_130_, v___x_106_);
if (v___x_131_ == 0)
{
lean_dec(v_id_127_);
goto v___jp_108_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = l_Lean_TSyntax_getId(v_id_127_);
lean_dec(v_id_127_);
v___x_133_ = l_Lean_Parser_getParserAliasInfo(v___x_132_);
lean_dec(v___x_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v_stackSz_x3f_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v_stackSz_x3f_135_ = lean_ctor_get(v_a_134_, 1);
lean_inc(v_stackSz_x3f_135_);
lean_dec(v_a_134_);
v___x_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_137_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_135_, v___x_136_);
lean_dec(v_stackSz_x3f_135_);
if (v___x_137_ == 0)
{
v_a_111_ = v___x_131_;
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
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v_b_94_);
v_a_138_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_150_ == 0)
{
v___x_140_ = v___x_133_;
v_isShared_141_ = v_isSharedCheck_150_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_133_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_150_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_ref_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v_ref_142_ = lean_ctor_get(v___y_95_, 7);
v___x_143_ = lean_io_error_to_string(v_a_138_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = l_Lean_MessageData_ofFormat(v___x_144_);
lean_inc(v_ref_142_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_ref_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_146_);
v___x_148_ = v___x_140_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_153_; 
v_id_153_ = l_Lean_Syntax_getArg(v___x_107_, v___x_105_);
if (v___x_90_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_153_);
v___x_166_ = l_Lean_Syntax_isOfKind(v_id_153_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_id_153_);
goto v___jp_108_;
}
else
{
goto v___jp_154_;
}
}
else
{
goto v___jp_154_;
}
v___jp_154_:
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
lean_dec(v_id_153_);
goto v___jp_108_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = l_Lean_Syntax_getArg(v___x_155_, v___x_105_);
lean_dec(v___x_155_);
v___x_159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_160_ = l_Lean_Syntax_isOfKind(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec(v_id_153_);
goto v___jp_108_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_153_, v___x_105_, v___x_124_, v___x_90_, v___x_161_, v___y_95_, v___y_96_);
lean_dec(v_id_153_);
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
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_153_, v___x_105_, v___x_124_, v___x_90_, v___x_163_, v___y_95_, v___y_96_);
lean_dec(v_id_153_);
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
lean_dec_ref_known(v___y_113_, 1);
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
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v_b_94_);
return v___x_167_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object* v___x_168_, lean_object* v_as_169_, lean_object* v_i_170_, lean_object* v_stop_171_, lean_object* v_b_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v___x_15404__boxed_176_; size_t v_i_boxed_177_; size_t v_stop_boxed_178_; lean_object* v_res_179_; 
v___x_15404__boxed_176_ = lean_unbox(v___x_168_);
v_i_boxed_177_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_171_);
lean_dec(v_stop_171_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_15404__boxed_176_, v_as_169_, v_i_boxed_177_, v_stop_boxed_178_, v_b_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v_as_169_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(uint8_t v___x_180_, lean_object* v_as_181_, size_t v_i_182_, size_t v_stop_183_, lean_object* v_b_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_a_189_; uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_eq(v_i_182_, v_stop_183_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v_a_201_; lean_object* v___y_203_; uint8_t v___x_214_; 
v___x_194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_array_uget_borrowed(v_as_181_, v_i_182_);
lean_inc(v___x_197_);
v___x_214_ = l_Lean_Syntax_isOfKind(v___x_197_, v___x_194_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_197_);
v___x_216_ = l_Lean_Syntax_isOfKind(v___x_197_, v___x_215_);
if (v___x_216_ == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v_id_217_; 
v_id_217_ = l_Lean_Syntax_getArg(v___x_197_, v___x_195_);
if (v___x_214_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_217_);
v___x_242_ = l_Lean_Syntax_isOfKind(v_id_217_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec(v_id_217_);
goto v___jp_198_;
}
else
{
goto v___jp_218_;
}
}
else
{
goto v___jp_218_;
}
v___jp_218_:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = l_Lean_Syntax_getArg(v___x_197_, v___x_219_);
v___x_221_ = l_Lean_Syntax_matchesNull(v___x_220_, v___x_196_);
if (v___x_221_ == 0)
{
lean_dec(v_id_217_);
goto v___jp_198_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = l_Lean_TSyntax_getId(v_id_217_);
lean_dec(v_id_217_);
v___x_223_ = l_Lean_Parser_getParserAliasInfo(v___x_222_);
lean_dec(v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v_stackSz_x3f_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v_stackSz_x3f_225_ = lean_ctor_get(v_a_224_, 1);
lean_inc(v_stackSz_x3f_225_);
lean_dec(v_a_224_);
v___x_226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_227_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_225_, v___x_226_);
lean_dec(v_stackSz_x3f_225_);
if (v___x_227_ == 0)
{
v_a_201_ = v___x_221_;
goto v___jp_200_;
}
else
{
v_a_201_ = v___x_214_;
goto v___jp_200_;
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_b_184_);
v_a_228_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_240_ == 0)
{
v___x_230_ = v___x_223_;
v_isShared_231_ = v_isSharedCheck_240_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_240_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_ref_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v_ref_232_ = lean_ctor_get(v___y_185_, 7);
v___x_233_ = lean_io_error_to_string(v_a_228_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = l_Lean_MessageData_ofFormat(v___x_234_);
lean_inc(v_ref_232_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_ref_232_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_236_);
v___x_238_ = v___x_230_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_id_243_ = l_Lean_Syntax_getArg(v___x_197_, v___x_195_);
v___x_244_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_243_);
v___x_245_ = l_Lean_Syntax_isOfKind(v_id_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_id_243_);
goto v___jp_198_;
}
else
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = l_Lean_Syntax_getArg(v___x_197_, v___x_196_);
v___x_247_ = l_Lean_Syntax_isNone(v___x_246_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
lean_inc(v___x_246_);
v___x_248_ = l_Lean_Syntax_matchesNull(v___x_246_, v___x_196_);
if (v___x_248_ == 0)
{
lean_dec(v___x_246_);
lean_dec(v_id_243_);
goto v___jp_198_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = l_Lean_Syntax_getArg(v___x_246_, v___x_195_);
lean_dec(v___x_246_);
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_251_ = l_Lean_Syntax_isOfKind(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_id_243_);
goto v___jp_198_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_box(0);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_243_, v___x_195_, v___x_214_, v___x_180_, v___x_252_, v___y_185_, v___y_186_);
lean_dec(v_id_243_);
v___y_203_ = v___x_253_;
goto v___jp_202_;
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_246_);
v___x_254_ = lean_box(0);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_243_, v___x_195_, v___x_214_, v___x_180_, v___x_254_, v___y_185_, v___y_186_);
lean_dec(v_id_243_);
v___y_203_ = v___x_255_;
goto v___jp_202_;
}
}
}
v___jp_198_:
{
lean_object* v___x_199_; 
lean_inc(v___x_197_);
v___x_199_ = lean_array_push(v_b_184_, v___x_197_);
v_a_189_ = v___x_199_;
goto v___jp_188_;
}
v___jp_200_:
{
if (v_a_201_ == 0)
{
v_a_189_ = v_b_184_;
goto v___jp_188_;
}
else
{
goto v___jp_198_;
}
}
v___jp_202_:
{
if (lean_obj_tag(v___y_203_) == 0)
{
lean_object* v_a_204_; uint8_t v___x_205_; 
v_a_204_ = lean_ctor_get(v___y_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref_known(v___y_203_, 1);
v___x_205_ = lean_unbox(v_a_204_);
lean_dec(v_a_204_);
v_a_201_ = v___x_205_;
goto v___jp_200_;
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec_ref(v_b_184_);
v_a_206_ = lean_ctor_get(v___y_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___y_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___y_203_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___y_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_b_184_);
return v___x_256_;
}
v___jp_188_:
{
size_t v___x_190_; size_t v___x_191_; 
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_182_, v___x_190_);
v_i_182_ = v___x_191_;
v_b_184_ = v_a_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object* v___x_257_, lean_object* v_as_258_, lean_object* v_i_259_, lean_object* v_stop_260_, lean_object* v_b_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_15598__boxed_265_; size_t v_i_boxed_266_; size_t v_stop_boxed_267_; lean_object* v_res_268_; 
v___x_15598__boxed_265_ = lean_unbox(v___x_257_);
v_i_boxed_266_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_stop_boxed_267_ = lean_unbox_usize(v_stop_260_);
lean_dec(v_stop_260_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_15598__boxed_265_, v_as_258_, v_i_boxed_266_, v_stop_boxed_267_, v_b_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_as_258_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(uint8_t v___x_269_, lean_object* v_as_270_, size_t v_i_271_, size_t v_stop_272_, lean_object* v_b_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_a_278_; uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_eq(v_i_271_, v_stop_272_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v_a_290_; lean_object* v___y_292_; uint8_t v___x_303_; 
v___x_283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_array_uget_borrowed(v_as_270_, v_i_271_);
lean_inc(v___x_286_);
v___x_303_ = l_Lean_Syntax_isOfKind(v___x_286_, v___x_283_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_286_);
v___x_305_ = l_Lean_Syntax_isOfKind(v___x_286_, v___x_304_);
if (v___x_305_ == 0)
{
goto v___jp_287_;
}
else
{
lean_object* v_id_306_; 
v_id_306_ = l_Lean_Syntax_getArg(v___x_286_, v___x_284_);
if (v___x_303_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_306_);
v___x_331_ = l_Lean_Syntax_isOfKind(v_id_306_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec(v_id_306_);
goto v___jp_287_;
}
else
{
goto v___jp_307_;
}
}
else
{
goto v___jp_307_;
}
v___jp_307_:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_unsigned_to_nat(2u);
v___x_309_ = l_Lean_Syntax_getArg(v___x_286_, v___x_308_);
v___x_310_ = l_Lean_Syntax_matchesNull(v___x_309_, v___x_285_);
if (v___x_310_ == 0)
{
lean_dec(v_id_306_);
goto v___jp_287_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Lean_TSyntax_getId(v_id_306_);
lean_dec(v_id_306_);
v___x_312_ = l_Lean_Parser_getParserAliasInfo(v___x_311_);
lean_dec(v___x_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_stackSz_x3f_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v_stackSz_x3f_314_ = lean_ctor_get(v_a_313_, 1);
lean_inc(v_stackSz_x3f_314_);
lean_dec(v_a_313_);
v___x_315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_316_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_314_, v___x_315_);
lean_dec(v_stackSz_x3f_314_);
if (v___x_316_ == 0)
{
v_a_290_ = v___x_310_;
goto v___jp_289_;
}
else
{
v_a_290_ = v___x_303_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v_b_273_);
v_a_317_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_329_ == 0)
{
v___x_319_ = v___x_312_;
v_isShared_320_ = v_isSharedCheck_329_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_312_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_329_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_ref_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v_ref_321_ = lean_ctor_get(v___y_274_, 7);
v___x_322_ = lean_io_error_to_string(v_a_317_);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___x_324_ = l_Lean_MessageData_ofFormat(v___x_323_);
lean_inc(v_ref_321_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_ref_321_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_325_);
v___x_327_ = v___x_319_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_332_; lean_object* v_id_333_; 
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v_id_333_ = l_Lean_Syntax_getArg(v___x_286_, v___x_284_);
if (v___x_269_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_333_);
v___x_345_ = l_Lean_Syntax_isOfKind(v_id_333_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec(v_id_333_);
goto v___jp_287_;
}
else
{
goto v___jp_334_;
}
}
else
{
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_Syntax_getArg(v___x_286_, v___x_285_);
v___x_336_ = l_Lean_Syntax_isNone(v___x_335_);
if (v___x_336_ == 0)
{
uint8_t v___x_337_; 
lean_inc(v___x_335_);
v___x_337_ = l_Lean_Syntax_matchesNull(v___x_335_, v___x_285_);
if (v___x_337_ == 0)
{
lean_dec(v___x_335_);
lean_dec(v_id_333_);
goto v___jp_287_;
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = l_Lean_Syntax_getArg(v___x_335_, v___x_284_);
lean_dec(v___x_335_);
v___x_339_ = l_Lean_Syntax_isOfKind(v___x_338_, v___x_332_);
if (v___x_339_ == 0)
{
lean_dec(v_id_333_);
goto v___jp_287_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_333_, v___x_284_, v___x_303_, v___x_269_, v___x_340_, v___y_274_, v___y_275_);
lean_dec(v_id_333_);
v___y_292_ = v___x_341_;
goto v___jp_291_;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v___x_335_);
v___x_342_ = lean_box(0);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_333_, v___x_284_, v___x_303_, v___x_269_, v___x_342_, v___y_274_, v___y_275_);
lean_dec(v_id_333_);
v___y_292_ = v___x_343_;
goto v___jp_291_;
}
}
}
v___jp_287_:
{
lean_object* v___x_288_; 
lean_inc(v___x_286_);
v___x_288_ = lean_array_push(v_b_273_, v___x_286_);
v_a_278_ = v___x_288_;
goto v___jp_277_;
}
v___jp_289_:
{
if (v_a_290_ == 0)
{
v_a_278_ = v_b_273_;
goto v___jp_277_;
}
else
{
goto v___jp_287_;
}
}
v___jp_291_:
{
if (lean_obj_tag(v___y_292_) == 0)
{
lean_object* v_a_293_; uint8_t v___x_294_; 
v_a_293_ = lean_ctor_get(v___y_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___y_292_, 1);
v___x_294_ = lean_unbox(v_a_293_);
lean_dec(v_a_293_);
v_a_290_ = v___x_294_;
goto v___jp_289_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_b_273_);
v_a_295_ = lean_ctor_get(v___y_292_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___y_292_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___y_292_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___y_292_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_b_273_);
return v___x_346_;
}
v___jp_277_:
{
size_t v___x_279_; size_t v___x_280_; 
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_271_, v___x_279_);
v_i_271_ = v___x_280_;
v_b_273_ = v_a_278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5___boxed(lean_object* v___x_347_, lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_stop_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_15776__boxed_355_; size_t v_i_boxed_356_; size_t v_stop_boxed_357_; lean_object* v_res_358_; 
v___x_15776__boxed_355_ = lean_unbox(v___x_347_);
v_i_boxed_356_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_357_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_15776__boxed_355_, v_as_348_, v_i_boxed_356_, v_stop_boxed_357_, v_b_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_as_348_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(lean_object* v_opts_359_, lean_object* v_opt_360_){
_start:
{
lean_object* v_name_361_; lean_object* v_defValue_362_; lean_object* v_map_363_; lean_object* v___x_364_; 
v_name_361_ = lean_ctor_get(v_opt_360_, 0);
v_defValue_362_ = lean_ctor_get(v_opt_360_, 1);
v_map_363_ = lean_ctor_get(v_opts_359_, 0);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_363_, v_name_361_);
if (lean_obj_tag(v___x_364_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = lean_unbox(v_defValue_362_);
return v___x_365_;
}
else
{
lean_object* v_val_366_; 
v_val_366_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_val_366_);
lean_dec_ref_known(v___x_364_, 1);
if (lean_obj_tag(v_val_366_) == 1)
{
uint8_t v_v_367_; 
v_v_367_ = lean_ctor_get_uint8(v_val_366_, 0);
lean_dec_ref_known(v_val_366_, 0);
return v_v_367_;
}
else
{
uint8_t v___x_368_; 
lean_dec(v_val_366_);
v___x_368_ = lean_unbox(v_defValue_362_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_369_, lean_object* v_opt_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_369_, v_opt_370_);
lean_dec_ref(v_opt_370_);
lean_dec_ref(v_opts_369_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_box(1);
v___x_374_ = l_Lean_MessageData_ofFormat(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2));
v___x_379_ = l_Lean_MessageData_ofFormat(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
return v_x_380_;
}
else
{
lean_object* v_head_382_; lean_object* v_tail_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_405_; 
v_head_382_ = lean_ctor_get(v_x_381_, 0);
v_tail_383_ = lean_ctor_get(v_x_381_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_405_ == 0)
{
v___x_385_ = v_x_381_;
v_isShared_386_ = v_isSharedCheck_405_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_tail_383_);
lean_inc(v_head_382_);
lean_dec(v_x_381_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_405_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_before_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_403_; 
v_before_387_ = lean_ctor_get(v_head_382_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_head_382_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_head_382_, 1);
lean_dec(v_unused_404_);
v___x_389_ = v_head_382_;
v_isShared_390_ = v_isSharedCheck_403_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_before_387_);
lean_dec(v_head_382_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_403_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 7);
lean_ctor_set(v___x_389_, 1, v___x_391_);
lean_ctor_set(v___x_389_, 0, v_x_380_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_x_380_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_402_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 7);
lean_ctor_set(v___x_385_, 1, v___x_394_);
lean_ctor_set(v___x_385_, 0, v___x_393_);
v___x_396_ = v___x_385_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = l_Lean_MessageData_ofSyntax(v_before_387_);
v___x_398_ = l_Lean_indentD(v___x_397_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_396_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v_x_380_ = v___x_399_;
v_x_381_ = v_tail_383_;
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
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1));
v___x_410_ = l_Lean_MessageData_ofFormat(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(lean_object* v_msgData_411_, lean_object* v_macroStack_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_scopes_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_opts_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_415_ = lean_st_ref_get(v___y_413_);
v_scopes_416_ = lean_ctor_get(v___x_415_, 2);
lean_inc(v_scopes_416_);
lean_dec(v___x_415_);
v___x_417_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_418_ = l_List_head_x21___redArg(v___x_417_, v_scopes_416_);
lean_dec(v_scopes_416_);
v_opts_419_ = lean_ctor_get(v___x_418_, 1);
lean_inc_ref(v_opts_419_);
lean_dec(v___x_418_);
v___x_420_ = l_Lean_Elab_pp_macroStack;
v___x_421_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_419_, v___x_420_);
lean_dec_ref(v_opts_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_macroStack_412_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_msgData_411_);
return v___x_422_;
}
else
{
if (lean_obj_tag(v_macroStack_412_) == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_msgData_411_);
return v___x_423_;
}
else
{
lean_object* v_head_424_; lean_object* v_after_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_440_; 
v_head_424_ = lean_ctor_get(v_macroStack_412_, 0);
lean_inc(v_head_424_);
v_after_425_ = lean_ctor_get(v_head_424_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v_head_424_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v_head_424_, 0);
lean_dec(v_unused_441_);
v___x_427_ = v_head_424_;
v_isShared_428_ = v_isSharedCheck_440_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_after_425_);
lean_dec(v_head_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_440_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 7);
lean_ctor_set(v___x_427_, 1, v___x_429_);
lean_ctor_set(v___x_427_, 0, v_msgData_411_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_msgData_411_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_439_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v_msgData_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_432_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_Lean_MessageData_ofSyntax(v_after_425_);
v___x_435_ = l_Lean_indentD(v___x_434_);
v_msgData_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_436_, 0, v___x_433_);
lean_ctor_set(v_msgData_436_, 1, v___x_435_);
v___x_437_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(v_msgData_436_, v_macroStack_412_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_442_, lean_object* v_macroStack_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_442_, v_macroStack_443_, v___y_444_);
lean_dec(v___y_444_);
return v_res_446_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_447_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
lean_ctor_set(v___x_452_, 3, v___x_451_);
lean_ctor_set(v___x_452_, 4, v___x_450_);
lean_ctor_set(v___x_452_, 5, v___x_450_);
lean_ctor_set(v___x_452_, 6, v___x_450_);
lean_ctor_set(v___x_452_, 7, v___x_450_);
lean_ctor_set(v___x_452_, 8, v___x_450_);
lean_ctor_set(v___x_452_, 9, v___x_450_);
lean_ctor_set(v___x_452_, 10, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(32u);
v___x_454_ = lean_mk_empty_array_with_capacity(v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_456_ = ((size_t)5ULL);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_unsigned_to_nat(32u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_461_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
lean_ctor_set(v___x_461_, 2, v___x_457_);
lean_ctor_set(v___x_461_, 3, v___x_457_);
lean_ctor_set_usize(v___x_461_, 4, v___x_456_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_box(1);
v___x_463_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_462_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; lean_object* v_env_470_; lean_object* v___x_471_; lean_object* v_scopes_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_opts_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_469_ = lean_st_ref_get(v___y_467_);
v_env_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_env_470_);
lean_dec(v___x_469_);
v___x_471_ = lean_st_ref_get(v___y_467_);
v_scopes_472_ = lean_ctor_get(v___x_471_, 2);
lean_inc(v_scopes_472_);
lean_dec(v___x_471_);
v___x_473_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_474_ = l_List_head_x21___redArg(v___x_473_, v_scopes_472_);
lean_dec(v_scopes_472_);
v_opts_475_ = lean_ctor_get(v___x_474_, 1);
lean_inc_ref(v_opts_475_);
lean_dec(v___x_474_);
v___x_476_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_477_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_478_, 0, v_env_470_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
lean_ctor_set(v___x_478_, 3, v_opts_475_);
v___x_479_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_msgData_466_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_481_, v___y_482_);
lean_dec(v___y_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Elab_Command_getRef___redArg(v___y_486_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v_macroStack_491_; lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v_macroStack_491_ = lean_ctor_get(v___y_486_, 4);
v___x_492_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_485_, v___y_487_);
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v___x_492_);
v___x_494_ = l_Lean_Elab_getBetterRef(v_a_490_, v_macroStack_491_);
lean_dec(v_a_490_);
lean_inc(v_macroStack_491_);
v___x_495_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_493_, v_macroStack_491_, v___y_487_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_494_);
lean_ctor_set(v___x_500_, 1, v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 1);
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v_msg_485_);
v_a_505_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_489_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_489_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t v___x_518_, lean_object* v_as_519_, size_t v_i_520_, size_t v_stop_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_a_527_; uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_eq(v_i_520_, v_stop_521_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v_a_537_; lean_object* v___y_539_; uint8_t v___x_550_; 
v___x_532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_533_ = lean_array_uget_borrowed(v_as_519_, v_i_520_);
lean_inc(v___x_533_);
v___x_550_ = l_Lean_Syntax_isOfKind(v___x_533_, v___x_532_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_533_);
v___x_552_ = l_Lean_Syntax_isOfKind(v___x_533_, v___x_551_);
if (v___x_552_ == 0)
{
goto v___jp_534_;
}
else
{
lean_object* v___x_553_; lean_object* v_id_554_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v_id_554_ = l_Lean_Syntax_getArg(v___x_533_, v___x_553_);
if (v___x_550_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_554_);
v___x_580_ = l_Lean_Syntax_isOfKind(v_id_554_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_id_554_);
goto v___jp_534_;
}
else
{
goto v___jp_555_;
}
}
else
{
goto v___jp_555_;
}
v___jp_555_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_unsigned_to_nat(2u);
v___x_558_ = l_Lean_Syntax_getArg(v___x_533_, v___x_557_);
v___x_559_ = l_Lean_Syntax_matchesNull(v___x_558_, v___x_556_);
if (v___x_559_ == 0)
{
lean_dec(v_id_554_);
goto v___jp_534_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Lean_TSyntax_getId(v_id_554_);
lean_dec(v_id_554_);
v___x_561_ = l_Lean_Parser_getParserAliasInfo(v___x_560_);
lean_dec(v___x_560_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v_stackSz_x3f_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v_stackSz_x3f_563_ = lean_ctor_get(v_a_562_, 1);
lean_inc(v_stackSz_x3f_563_);
lean_dec(v_a_562_);
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_565_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_563_, v___x_564_);
lean_dec(v_stackSz_x3f_563_);
if (v___x_565_ == 0)
{
v_a_537_ = v___x_559_;
goto v___jp_536_;
}
else
{
v_a_537_ = v___x_550_;
goto v___jp_536_;
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_b_522_);
v_a_566_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_578_ == 0)
{
v___x_568_ = v___x_561_;
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_ref_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v_ref_570_ = lean_ctor_get(v___y_523_, 7);
v___x_571_ = lean_io_error_to_string(v_a_566_);
v___x_572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = l_Lean_MessageData_ofFormat(v___x_572_);
lean_inc(v_ref_570_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_ref_570_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_574_);
v___x_576_ = v___x_568_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_581_; lean_object* v_id_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v_id_582_ = l_Lean_Syntax_getArg(v___x_533_, v___x_581_);
if (v___x_518_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_582_);
v___x_596_ = l_Lean_Syntax_isOfKind(v_id_582_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v_id_582_);
goto v___jp_534_;
}
else
{
goto v___jp_583_;
}
}
else
{
goto v___jp_583_;
}
v___jp_583_:
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = l_Lean_Syntax_getArg(v___x_533_, v___x_584_);
v___x_586_ = l_Lean_Syntax_isNone(v___x_585_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
lean_inc(v___x_585_);
v___x_587_ = l_Lean_Syntax_matchesNull(v___x_585_, v___x_584_);
if (v___x_587_ == 0)
{
lean_dec(v___x_585_);
lean_dec(v_id_582_);
goto v___jp_534_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = l_Lean_Syntax_getArg(v___x_585_, v___x_581_);
lean_dec(v___x_585_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_590_ = l_Lean_Syntax_isOfKind(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec(v_id_582_);
goto v___jp_534_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(0);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_582_, v___x_581_, v___x_550_, v___x_518_, v___x_591_, v___y_523_, v___y_524_);
lean_dec(v_id_582_);
v___y_539_ = v___x_592_;
goto v___jp_538_;
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v___x_585_);
v___x_593_ = lean_box(0);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_582_, v___x_581_, v___x_550_, v___x_518_, v___x_593_, v___y_523_, v___y_524_);
lean_dec(v_id_582_);
v___y_539_ = v___x_594_;
goto v___jp_538_;
}
}
}
v___jp_534_:
{
lean_object* v___x_535_; 
lean_inc(v___x_533_);
v___x_535_ = lean_array_push(v_b_522_, v___x_533_);
v_a_527_ = v___x_535_;
goto v___jp_526_;
}
v___jp_536_:
{
if (v_a_537_ == 0)
{
v_a_527_ = v_b_522_;
goto v___jp_526_;
}
else
{
goto v___jp_534_;
}
}
v___jp_538_:
{
if (lean_obj_tag(v___y_539_) == 0)
{
lean_object* v_a_540_; uint8_t v___x_541_; 
v_a_540_ = lean_ctor_get(v___y_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___y_539_, 1);
v___x_541_ = lean_unbox(v_a_540_);
lean_dec(v_a_540_);
v_a_537_ = v___x_541_;
goto v___jp_536_;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_b_522_);
v_a_542_ = lean_ctor_get(v___y_539_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___y_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___y_539_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___y_539_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v_b_522_);
return v___x_597_;
}
v___jp_526_:
{
size_t v___x_528_; size_t v___x_529_; 
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_520_, v___x_528_);
v_i_520_ = v___x_529_;
v_b_522_ = v_a_527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v___x_598_, lean_object* v_as_599_, lean_object* v_i_600_, lean_object* v_stop_601_, lean_object* v_b_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
uint8_t v___x_16264__boxed_606_; size_t v_i_boxed_607_; size_t v_stop_boxed_608_; lean_object* v_res_609_; 
v___x_16264__boxed_606_ = lean_unbox(v___x_598_);
v_i_boxed_607_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_stop_boxed_608_ = lean_unbox_usize(v_stop_601_);
lean_dec(v_stop_601_);
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_16264__boxed_606_, v_as_599_, v_i_boxed_607_, v_stop_boxed_608_, v_b_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec_ref(v_as_599_);
return v_res_609_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(0);
v___x_623_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; uint8_t v___x_640_; 
v___x_636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_631_);
v___x_639_ = l_Lean_Syntax_isOfKind(v_a_631_, v___x_638_);
v___x_640_ = 1;
if (v___x_639_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_631_);
v___x_648_ = l_Lean_Syntax_isOfKind(v_a_631_, v___x_647_);
if (v___x_648_ == 0)
{
lean_dec(v_a_631_);
goto v___jp_641_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_a_654_; lean_object* v___y_660_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = l_Lean_Syntax_getArg(v_a_631_, v___x_649_);
lean_dec(v_a_631_);
v___x_651_ = l_Lean_Syntax_getArgs(v___x_650_);
lean_dec(v___x_650_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_array_get_size(v___x_651_);
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_672_ = lean_nat_dec_lt(v___x_652_, v___x_670_);
if (v___x_672_ == 0)
{
lean_dec_ref(v___x_651_);
v_a_654_ = v___x_671_;
goto v___jp_653_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_le(v___x_670_, v___x_670_);
if (v___x_673_ == 0)
{
if (v___x_672_ == 0)
{
lean_dec_ref(v___x_651_);
v_a_654_ = v___x_671_;
goto v___jp_653_;
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_670_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_639_, v___x_651_, v___x_674_, v___x_675_, v___x_671_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_651_);
v___y_660_ = v___x_676_;
goto v___jp_659_;
}
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_670_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_639_, v___x_651_, v___x_677_, v___x_678_, v___x_671_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_651_);
v___y_660_ = v___x_679_;
goto v___jp_659_;
}
}
v___jp_653_:
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_array_get_size(v_a_654_);
v___x_656_ = lean_nat_dec_eq(v___x_655_, v___x_649_);
if (v___x_656_ == 0)
{
lean_dec_ref(v_a_654_);
goto v___jp_641_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = lean_array_fget(v_a_654_, v___x_652_);
lean_dec_ref(v_a_654_);
v_a_631_ = v___x_657_;
goto _start;
}
}
v___jp_659_:
{
if (lean_obj_tag(v___y_660_) == 0)
{
lean_object* v_a_661_; 
v_a_661_ = lean_ctor_get(v___y_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___y_660_, 1);
v_a_654_ = v_a_661_;
goto v___jp_653_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_a_632_);
v_a_662_ = lean_ctor_get(v___y_660_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___y_660_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___y_660_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___y_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
else
{
lean_object* v___x_680_; lean_object* v___y_692_; lean_object* v___y_698_; lean_object* v_id_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v_id_708_ = l_Lean_Syntax_getArg(v_a_631_, v___x_680_);
v___x_709_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_708_);
v___x_711_ = l_Lean_Syntax_isOfKind(v_id_708_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
lean_dec(v_id_708_);
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_631_);
v___x_713_ = l_Lean_Syntax_isOfKind(v_a_631_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v_a_631_);
goto v___jp_703_;
}
else
{
lean_object* v___x_714_; lean_object* v_a_716_; lean_object* v___y_722_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_732_ = l_Lean_Syntax_getArg(v_a_631_, v___x_714_);
lean_dec(v_a_631_);
v___x_733_ = l_Lean_Syntax_getArgs(v___x_732_);
lean_dec(v___x_732_);
v___x_734_ = lean_array_get_size(v___x_733_);
v___x_735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_736_ = lean_nat_dec_lt(v___x_680_, v___x_734_);
if (v___x_736_ == 0)
{
lean_dec_ref(v___x_733_);
v_a_716_ = v___x_735_;
goto v___jp_715_;
}
else
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_le(v___x_734_, v___x_734_);
if (v___x_737_ == 0)
{
if (v___x_736_ == 0)
{
lean_dec_ref(v___x_733_);
v_a_716_ = v___x_735_;
goto v___jp_715_;
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_734_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_711_, v___x_733_, v___x_738_, v___x_739_, v___x_735_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_733_);
v___y_722_ = v___x_740_;
goto v___jp_721_;
}
}
else
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_734_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_711_, v___x_733_, v___x_741_, v___x_742_, v___x_735_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_733_);
v___y_722_ = v___x_743_;
goto v___jp_721_;
}
}
v___jp_715_:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_array_get_size(v_a_716_);
v___x_718_ = lean_nat_dec_eq(v___x_717_, v___x_714_);
if (v___x_718_ == 0)
{
lean_dec_ref(v_a_716_);
goto v___jp_703_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_array_fget(v_a_716_, v___x_680_);
lean_dec_ref(v_a_716_);
v_a_631_ = v___x_719_;
goto _start;
}
}
v___jp_721_:
{
if (lean_obj_tag(v___y_722_) == 0)
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v___y_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___y_722_, 1);
v_a_716_ = v_a_723_;
goto v___jp_715_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_632_);
v_a_724_ = lean_ctor_get(v___y_722_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___y_722_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___y_722_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___y_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
else
{
lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___x_826_; lean_object* v_a_828_; lean_object* v___y_834_; lean_object* v_a_845_; lean_object* v___y_851_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_861_ = l_Lean_Syntax_getArg(v_a_631_, v___x_826_);
v___x_862_ = l_Lean_Syntax_isNone(v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
lean_inc(v___x_861_);
v___x_863_ = l_Lean_Syntax_matchesNull(v___x_861_, v___x_826_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
lean_dec(v_id_708_);
v___x_864_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_865_ = l_Lean_Syntax_isOfKind(v_a_631_, v___x_864_);
if (v___x_865_ == 0)
{
lean_dec(v___x_861_);
goto v___jp_686_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_866_ = l_Lean_Syntax_getArgs(v___x_861_);
lean_dec(v___x_861_);
v___x_867_ = lean_array_get_size(v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_869_ = lean_nat_dec_lt(v___x_680_, v___x_867_);
if (v___x_869_ == 0)
{
lean_dec_ref(v___x_866_);
v_a_845_ = v___x_868_;
goto v___jp_844_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = lean_nat_dec_le(v___x_867_, v___x_867_);
if (v___x_870_ == 0)
{
if (v___x_869_ == 0)
{
lean_dec_ref(v___x_866_);
v_a_845_ = v___x_868_;
goto v___jp_844_;
}
else
{
size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
v___x_871_ = ((size_t)0ULL);
v___x_872_ = lean_usize_of_nat(v___x_867_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_863_, v___x_866_, v___x_871_, v___x_872_, v___x_868_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_866_);
v___y_851_ = v___x_873_;
goto v___jp_850_;
}
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_867_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_863_, v___x_866_, v___x_874_, v___x_875_, v___x_868_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_866_);
v___y_851_ = v___x_876_;
goto v___jp_850_;
}
}
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = l_Lean_Syntax_getArg(v___x_861_, v___x_680_);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_879_ = l_Lean_Syntax_isOfKind(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; uint8_t v___x_881_; 
lean_dec(v_id_708_);
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_881_ = l_Lean_Syntax_isOfKind(v_a_631_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v___x_861_);
goto v___jp_681_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_882_ = l_Lean_Syntax_getArgs(v___x_861_);
lean_dec(v___x_861_);
v___x_883_ = lean_array_get_size(v___x_882_);
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_885_ = lean_nat_dec_lt(v___x_680_, v___x_883_);
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_882_);
v_a_828_ = v___x_884_;
goto v___jp_827_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = lean_nat_dec_le(v___x_883_, v___x_883_);
if (v___x_886_ == 0)
{
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_882_);
v_a_828_ = v___x_884_;
goto v___jp_827_;
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_of_nat(v___x_883_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_879_, v___x_882_, v___x_887_, v___x_888_, v___x_884_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_882_);
v___y_834_ = v___x_889_;
goto v___jp_833_;
}
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_883_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_879_, v___x_882_, v___x_890_, v___x_891_, v___x_884_, v_a_633_, v_a_634_);
lean_dec_ref(v___x_882_);
v___y_834_ = v___x_892_;
goto v___jp_833_;
}
}
}
}
else
{
lean_dec(v___x_861_);
lean_dec(v_a_631_);
v___y_745_ = v_a_633_;
v___y_746_ = v_a_634_;
goto v___jp_744_;
}
}
}
else
{
lean_dec(v___x_861_);
lean_dec(v_a_631_);
v___y_745_ = v_a_633_;
v___y_746_ = v_a_634_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_inc(v_id_708_);
v___x_747_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_747_, 0, v_id_708_);
v___x_748_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_747_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_817_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_817_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_817_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_817_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
if (lean_obj_tag(v_a_749_) == 1)
{
lean_object* v_val_753_; 
v_val_753_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_a_749_, 1);
switch(lean_obj_tag(v_val_753_))
{
case 0:
{
lean_object* v_cat_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec(v_id_708_);
v_cat_754_ = lean_ctor_get(v_val_753_, 0);
lean_inc(v_cat_754_);
lean_dec_ref_known(v_val_753_, 1);
v___x_755_ = lean_box(0);
v___x_756_ = l_Lean_Syntax_mkAntiquotNode(v_cat_754_, v_a_632_, v___x_680_, v___x_755_, v___x_640_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_756_);
v___x_758_ = v___x_751_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
case 1:
{
lean_object* v_decl_760_; 
lean_del_object(v___x_751_);
lean_dec(v_id_708_);
v_decl_760_ = lean_ctor_get(v_val_753_, 0);
lean_inc(v_decl_760_);
lean_dec_ref_known(v_val_753_, 1);
if (lean_obj_tag(v_decl_760_) == 1)
{
lean_object* v_pre_761_; 
v_pre_761_ = lean_ctor_get(v_decl_760_, 0);
if (lean_obj_tag(v_pre_761_) == 1)
{
lean_object* v_pre_762_; 
v_pre_762_ = lean_ctor_get(v_pre_761_, 0);
if (lean_obj_tag(v_pre_762_) == 1)
{
lean_object* v_pre_763_; 
v_pre_763_ = lean_ctor_get(v_pre_762_, 0);
switch(lean_obj_tag(v_pre_763_))
{
case 0:
{
lean_object* v_str_764_; lean_object* v_str_765_; lean_object* v_str_766_; uint8_t v___x_767_; 
v_str_764_ = lean_ctor_get(v_decl_760_, 1);
v_str_765_ = lean_ctor_get(v_pre_761_, 1);
v_str_766_ = lean_ctor_get(v_pre_762_, 1);
v___x_767_ = lean_string_dec_eq(v_str_766_, v___x_636_);
if (v___x_767_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
uint8_t v___x_768_; 
v___x_768_ = lean_string_dec_eq(v_str_765_, v___x_637_);
if (v___x_768_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_string_dec_eq(v_str_764_, v___x_709_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_771_ = lean_string_dec_eq(v_str_764_, v___x_770_);
if (v___x_771_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
lean_object* v___x_772_; 
lean_dec_ref_known(v_decl_760_, 2);
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_692_ = v___x_772_;
goto v___jp_691_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec_ref_known(v_decl_760_, 2);
v___x_773_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_692_ = v___x_773_;
goto v___jp_691_;
}
}
}
}
case 1:
{
lean_object* v_pre_774_; 
v_pre_774_ = lean_ctor_get(v_pre_763_, 0);
if (lean_obj_tag(v_pre_774_) == 0)
{
lean_object* v_str_775_; lean_object* v_str_776_; lean_object* v_str_777_; lean_object* v_str_778_; uint8_t v___x_779_; 
v_str_775_ = lean_ctor_get(v_decl_760_, 1);
v_str_776_ = lean_ctor_get(v_pre_761_, 1);
v_str_777_ = lean_ctor_get(v_pre_762_, 1);
v_str_778_ = lean_ctor_get(v_pre_763_, 1);
v___x_779_ = lean_string_dec_eq(v_str_778_, v___x_636_);
if (v___x_779_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = lean_string_dec_eq(v_str_777_, v___x_637_);
if (v___x_780_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_782_ = lean_string_dec_eq(v_str_776_, v___x_781_);
if (v___x_782_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_string_dec_eq(v_str_775_, v___x_709_);
if (v___x_783_ == 0)
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
else
{
lean_object* v___x_784_; 
lean_dec_ref_known(v_decl_760_, 2);
v___x_784_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_692_ = v___x_784_;
goto v___jp_691_;
}
}
}
}
}
else
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
}
default: 
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
}
}
else
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
}
else
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
}
else
{
v___y_692_ = v_decl_760_;
goto v___jp_691_;
}
}
default: 
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_751_);
v_isSharedCheck_809_ = !lean_is_exclusive(v_val_753_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_val_753_, 0);
lean_dec(v_unused_810_);
v___x_786_ = v_val_753_;
v_isShared_787_ = v_isSharedCheck_809_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_val_753_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_809_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = l_Lean_TSyntax_getId(v_id_708_);
lean_dec(v_id_708_);
v___x_789_ = l_Lean_Name_eraseMacroScopes(v___x_788_);
lean_dec(v___x_788_);
v___x_790_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_789_);
lean_dec(v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; 
lean_del_object(v___x_786_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
if (lean_obj_tag(v_a_791_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_box(0);
v___y_698_ = v___x_792_;
goto v___jp_697_;
}
else
{
lean_object* v_val_793_; 
v_val_793_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_a_791_, 1);
v___y_698_ = v_val_793_;
goto v___jp_697_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_a_632_);
v_a_794_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_808_ == 0)
{
v___x_796_ = v___x_790_;
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_790_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_ref_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v_ref_798_ = lean_ctor_get(v___y_745_, 7);
v___x_799_ = lean_io_error_to_string(v_a_794_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 3);
lean_ctor_set(v___x_786_, 0, v___x_799_);
v___x_801_ = v___x_786_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_807_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = l_Lean_MessageData_ofFormat(v___x_801_);
lean_inc(v_ref_798_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_ref_798_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_803_);
v___x_805_ = v___x_796_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
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
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_del_object(v___x_751_);
lean_dec(v_a_749_);
lean_dec(v_a_632_);
v___x_811_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_812_ = l_Lean_MessageData_ofSyntax(v_id_708_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_815_, v___y_745_, v___y_746_);
return v___x_816_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_id_708_);
lean_dec(v_a_632_);
v_a_818_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_748_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_748_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
v___jp_827_:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_array_get_size(v_a_828_);
v___x_830_ = lean_nat_dec_eq(v___x_829_, v___x_826_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_a_828_);
goto v___jp_681_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_array_fget(v_a_828_, v___x_680_);
lean_dec_ref(v_a_828_);
v_a_631_ = v___x_831_;
goto _start;
}
}
v___jp_833_:
{
if (lean_obj_tag(v___y_834_) == 0)
{
lean_object* v_a_835_; 
v_a_835_ = lean_ctor_get(v___y_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___y_834_, 1);
v_a_828_ = v_a_835_;
goto v___jp_827_;
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec(v_a_632_);
v_a_836_ = lean_ctor_get(v___y_834_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___y_834_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___y_834_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___y_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
v___jp_844_:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_get_size(v_a_845_);
v___x_847_ = lean_nat_dec_eq(v___x_846_, v___x_826_);
if (v___x_847_ == 0)
{
lean_dec_ref(v_a_845_);
goto v___jp_686_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = lean_array_fget(v_a_845_, v___x_680_);
lean_dec_ref(v_a_845_);
v_a_631_ = v___x_848_;
goto _start;
}
}
v___jp_850_:
{
if (lean_obj_tag(v___y_851_) == 0)
{
lean_object* v_a_852_; 
v_a_852_ = lean_ctor_get(v___y_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___y_851_, 1);
v_a_845_ = v_a_852_;
goto v___jp_844_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_a_632_);
v_a_853_ = lean_ctor_get(v___y_851_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___y_851_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___y_851_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___y_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
v___jp_681_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = lean_box(0);
v___x_683_ = lean_box(0);
v___x_684_ = l_Lean_Syntax_mkAntiquotNode(v___x_682_, v_a_632_, v___x_680_, v___x_683_, v___x_640_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_box(0);
v___x_689_ = l_Lean_Syntax_mkAntiquotNode(v___x_687_, v_a_632_, v___x_680_, v___x_688_, v___x_640_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
v___jp_691_:
{
lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_box(0);
v___x_694_ = 0;
v___x_695_ = l_Lean_Syntax_mkAntiquotNode(v___y_692_, v_a_632_, v___x_680_, v___x_693_, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
v___jp_697_:
{
lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_box(0);
v___x_700_ = 0;
v___x_701_ = l_Lean_Syntax_mkAntiquotNode(v___y_698_, v_a_632_, v___x_680_, v___x_699_, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
v___jp_703_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_Syntax_mkAntiquotNode(v___x_704_, v_a_632_, v___x_680_, v___x_705_, v___x_640_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
v___jp_641_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_642_ = lean_box(0);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_box(0);
v___x_645_ = l_Lean_Syntax_mkAntiquotNode(v___x_642_, v_a_632_, v___x_643_, v___x_644_, v___x_640_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_899_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_909_, lean_object* v_msg_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_915_, lean_object* v_msg_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_915_, v_msg_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_921_, lean_object* v_macroStack_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_921_, v_macroStack_922_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_927_, lean_object* v_macroStack_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_927_, v_macroStack_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_936_, lean_object* v_stx_937_, lean_object* v_id_938_, lean_object* v_suffix_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_937_, v_id_938_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_958_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_958_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_948_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_936_, v_a_944_, v_suffix_939_);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_949_);
v___x_951_ = lean_array_push(v___x_950_, v___x_948_);
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_953_ = lean_box(2);
v___x_954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
lean_ctor_set(v___x_954_, 2, v___x_951_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_954_);
v___x_956_ = v___x_946_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_dec_ref(v_suffix_939_);
lean_dec(v_kind_936_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_959_, lean_object* v_stx_960_, lean_object* v_id_961_, lean_object* v_suffix_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_959_, v_stx_960_, v_id_961_, v_suffix_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_env_970_; lean_object* v___x_971_; lean_object* v_mainModule_972_; lean_object* v___x_973_; 
v___x_969_ = lean_st_ref_get(v___y_967_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v___x_971_ = l_Lean_Environment_header(v_env_970_);
lean_dec_ref(v_env_970_);
v_mainModule_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_mainModule_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_mainModule_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_974_);
lean_dec(v___y_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_988_ = lean_panic_fn_borrowed(v___x_987_, v_msg_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = l_Lean_maxRecDepthErrorMessage;
v___x_995_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_997_ = l_Lean_MessageData_ofFormat(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_999_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_1000_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_ref_1001_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_1009_, lean_object* v_declName_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___x_1013_; lean_object* v_env_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1013_ = 0;
v_env_1014_ = l_Lean_Environment_setExporting(v_env_1009_, v___x_1013_);
lean_inc(v_declName_1010_);
v___x_1015_ = l_Lean_mkPrivateName(v_env_1014_, v_declName_1010_);
v___x_1016_ = 1;
lean_inc_ref(v_env_1014_);
v___x_1017_ = l_Lean_Environment_contains(v_env_1014_, v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = l_Lean_privateToUserName(v_declName_1010_);
v___x_1019_ = l_Lean_Environment_contains(v_env_1014_, v___x_1018_, v___x_1016_);
v___x_1020_ = lean_box(v___x_1019_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___y_1012_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v_env_1014_);
lean_dec(v_declName_1010_);
v___x_1022_ = lean_box(v___x_1017_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___y_1012_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_1024_, lean_object* v_declName_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1024_, v_declName_1025_, v___y_1026_, v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_1029_, lean_object* v_i_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_array_get_size(v_keys_1029_);
v___x_1033_ = lean_nat_dec_lt(v_i_1030_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_dec(v_i_1030_);
return v___x_1033_;
}
else
{
lean_object* v_k_x27_1034_; uint8_t v___x_1035_; 
v_k_x27_1034_ = lean_array_fget_borrowed(v_keys_1029_, v_i_1030_);
v___x_1035_ = l_Lean_instBEqExtraModUse_beq(v_k_1031_, v_k_x27_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_nat_add(v_i_1030_, v___x_1036_);
lean_dec(v_i_1030_);
v_i_1030_ = v___x_1037_;
goto _start;
}
else
{
lean_dec(v_i_1030_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_1039_, lean_object* v_i_1040_, lean_object* v_k_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_1039_, v_i_1040_, v_k_1041_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_keys_1039_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_1044_, size_t v_x_1045_, lean_object* v_x_1046_){
_start:
{
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_object* v_es_1047_; lean_object* v___x_1048_; size_t v___x_1049_; size_t v___x_1050_; lean_object* v_j_1051_; lean_object* v___x_1052_; 
v_es_1047_ = lean_ctor_get(v_x_1044_, 0);
v___x_1048_ = lean_box(2);
v___x_1049_ = ((size_t)31ULL);
v___x_1050_ = lean_usize_land(v_x_1045_, v___x_1049_);
v_j_1051_ = lean_usize_to_nat(v___x_1050_);
v___x_1052_ = lean_array_get_borrowed(v___x_1048_, v_es_1047_, v_j_1051_);
lean_dec(v_j_1051_);
switch(lean_obj_tag(v___x_1052_))
{
case 0:
{
lean_object* v_key_1053_; uint8_t v___x_1054_; 
v_key_1053_ = lean_ctor_get(v___x_1052_, 0);
v___x_1054_ = l_Lean_instBEqExtraModUse_beq(v_x_1046_, v_key_1053_);
return v___x_1054_;
}
case 1:
{
lean_object* v_node_1055_; size_t v___x_1056_; size_t v___x_1057_; 
v_node_1055_ = lean_ctor_get(v___x_1052_, 0);
v___x_1056_ = ((size_t)5ULL);
v___x_1057_ = lean_usize_shift_right(v_x_1045_, v___x_1056_);
v_x_1044_ = v_node_1055_;
v_x_1045_ = v___x_1057_;
goto _start;
}
default: 
{
uint8_t v___x_1059_; 
v___x_1059_ = 0;
return v___x_1059_;
}
}
}
else
{
lean_object* v_ks_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_ks_1060_ = lean_ctor_get(v_x_1044_, 0);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_1060_, v___x_1061_, v_x_1046_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
size_t v_x_42447__boxed_1066_; uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_x_42447__boxed_1066_ = lean_unbox_usize(v_x_1064_);
lean_dec(v_x_1064_);
v_res_1067_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1063_, v_x_42447__boxed_1066_, v_x_1065_);
lean_dec_ref(v_x_1065_);
lean_dec_ref(v_x_1063_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint64_t v___x_1071_; size_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = l_Lean_instHashableExtraModUse_hash(v_x_1070_);
v___x_1072_ = lean_uint64_to_usize(v___x_1071_);
v___x_1073_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1069_, v___x_1072_, v_x_1070_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_1074_, v_x_1075_);
lean_dec_ref(v_x_1075_);
lean_dec_ref(v_x_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1078_; double v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_float_of_nat(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_1082_, lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Elab_Command_getRef___redArg(v___y_1084_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1137_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_1083_, v___y_1085_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1137_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1137_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v_traceState_1095_; lean_object* v_env_1096_; lean_object* v_messages_1097_; lean_object* v_scopes_1098_; lean_object* v_usedQuotCtxts_1099_; lean_object* v_nextMacroScope_1100_; lean_object* v_maxRecDepth_1101_; lean_object* v_ngen_1102_; lean_object* v_auxDeclNGen_1103_; lean_object* v_infoState_1104_; lean_object* v_snapshotTasks_1105_; lean_object* v_prevLinterStates_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1136_; 
v___x_1094_ = lean_st_ref_take(v___y_1085_);
v_traceState_1095_ = lean_ctor_get(v___x_1094_, 9);
v_env_1096_ = lean_ctor_get(v___x_1094_, 0);
v_messages_1097_ = lean_ctor_get(v___x_1094_, 1);
v_scopes_1098_ = lean_ctor_get(v___x_1094_, 2);
v_usedQuotCtxts_1099_ = lean_ctor_get(v___x_1094_, 3);
v_nextMacroScope_1100_ = lean_ctor_get(v___x_1094_, 4);
v_maxRecDepth_1101_ = lean_ctor_get(v___x_1094_, 5);
v_ngen_1102_ = lean_ctor_get(v___x_1094_, 6);
v_auxDeclNGen_1103_ = lean_ctor_get(v___x_1094_, 7);
v_infoState_1104_ = lean_ctor_get(v___x_1094_, 8);
v_snapshotTasks_1105_ = lean_ctor_get(v___x_1094_, 10);
v_prevLinterStates_1106_ = lean_ctor_get(v___x_1094_, 11);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1108_ = v___x_1094_;
v_isShared_1109_ = v_isSharedCheck_1136_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_prevLinterStates_1106_);
lean_inc(v_snapshotTasks_1105_);
lean_inc(v_traceState_1095_);
lean_inc(v_infoState_1104_);
lean_inc(v_auxDeclNGen_1103_);
lean_inc(v_ngen_1102_);
lean_inc(v_maxRecDepth_1101_);
lean_inc(v_nextMacroScope_1100_);
lean_inc(v_usedQuotCtxts_1099_);
lean_inc(v_scopes_1098_);
lean_inc(v_messages_1097_);
lean_inc(v_env_1096_);
lean_dec(v___x_1094_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1136_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
uint64_t v_tid_1110_; lean_object* v_traces_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1135_; 
v_tid_1110_ = lean_ctor_get_uint64(v_traceState_1095_, sizeof(void*)*1);
v_traces_1111_ = lean_ctor_get(v_traceState_1095_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_traceState_1095_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1113_ = v_traceState_1095_;
v_isShared_1114_ = v_isSharedCheck_1135_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_traces_1111_);
lean_dec(v_traceState_1095_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1135_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; double v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_1117_ = 0;
v___x_1118_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1119_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1119_, 0, v_cls_1082_);
lean_ctor_set(v___x_1119_, 1, v___x_1115_);
lean_ctor_set(v___x_1119_, 2, v___x_1118_);
lean_ctor_set_float(v___x_1119_, sizeof(void*)*3, v___x_1116_);
lean_ctor_set_float(v___x_1119_, sizeof(void*)*3 + 8, v___x_1116_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*3 + 16, v___x_1117_);
v___x_1120_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_1121_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v_a_1090_);
lean_ctor_set(v___x_1121_, 2, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_a_1088_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_PersistentArray_push___redArg(v_traces_1111_, v___x_1122_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1123_);
v___x_1125_ = v___x_1113_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1123_);
lean_ctor_set_uint64(v_reuseFailAlloc_1134_, sizeof(void*)*1, v_tid_1110_);
v___x_1125_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 9, v___x_1125_);
v___x_1127_ = v___x_1108_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_env_1096_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_messages_1097_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_scopes_1098_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_usedQuotCtxts_1099_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_nextMacroScope_1100_);
lean_ctor_set(v_reuseFailAlloc_1133_, 5, v_maxRecDepth_1101_);
lean_ctor_set(v_reuseFailAlloc_1133_, 6, v_ngen_1102_);
lean_ctor_set(v_reuseFailAlloc_1133_, 7, v_auxDeclNGen_1103_);
lean_ctor_set(v_reuseFailAlloc_1133_, 8, v_infoState_1104_);
lean_ctor_set(v_reuseFailAlloc_1133_, 9, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1133_, 10, v_snapshotTasks_1105_);
lean_ctor_set(v_reuseFailAlloc_1133_, 11, v_prevLinterStates_1106_);
v___x_1127_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1128_ = lean_st_ref_put(v___y_1085_, v___x_1127_);
v___x_1129_ = lean_box(0);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1129_);
v___x_1131_ = v___x_1092_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_msg_1083_);
lean_dec(v_cls_1082_);
v_a_1138_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1087_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1087_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1146_, v_msg_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1151_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1));
v___x_1155_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0));
v___x_1156_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1155_, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v_cls_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_cls_1169_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4));
v___x_1170_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1171_ = l_Lean_Name_append(v___x_1170_, v_cls_1169_);
return v___x_1171_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1182_, uint8_t v_isMeta_1183_, lean_object* v_hint_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; uint8_t v_isExporting_1190_; lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v___x_1193_; lean_object* v_entry_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___y_1199_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1188_ = lean_st_ref_get(v___y_1186_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_env_1189_);
lean_dec(v___x_1188_);
v_isExporting_1190_ = lean_ctor_get_uint8(v_env_1189_, sizeof(void*)*8);
lean_dec_ref(v_env_1189_);
v___x_1191_ = lean_st_ref_get(v___y_1186_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2);
lean_inc(v_mod_1182_);
v_entry_1194_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1194_, 0, v_mod_1182_);
lean_ctor_set_uint8(v_entry_1194_, sizeof(void*)*1, v_isExporting_1190_);
lean_ctor_set_uint8(v_entry_1194_, sizeof(void*)*1 + 1, v_isMeta_1183_);
v___x_1195_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1196_ = lean_box(1);
v___x_1197_ = lean_box(0);
v___x_1226_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1193_, v___x_1195_, v_env_1192_, v___x_1196_, v___x_1197_);
v___x_1227_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1226_, v_entry_1194_);
lean_dec(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_scopes_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_opts_1234_; uint8_t v_hasTrace_1235_; 
v___x_1228_ = l_Lean_inheritedTraceOptions;
v___x_1229_ = lean_st_ref_get(v___x_1228_);
v___x_1230_ = lean_st_ref_get(v___y_1186_);
v_scopes_1231_ = lean_ctor_get(v___x_1230_, 2);
lean_inc(v_scopes_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1233_ = l_List_head_x21___redArg(v___x_1232_, v_scopes_1231_);
lean_dec(v_scopes_1231_);
v_opts_1234_ = lean_ctor_get(v___x_1233_, 1);
lean_inc_ref(v_opts_1234_);
lean_dec(v___x_1233_);
v_hasTrace_1235_ = lean_ctor_get_uint8(v_opts_1234_, sizeof(void*)*1);
if (v_hasTrace_1235_ == 0)
{
lean_dec_ref(v_opts_1234_);
lean_dec(v___x_1229_);
lean_dec(v_hint_1184_);
lean_dec(v_mod_1182_);
v___y_1199_ = v___y_1186_;
goto v___jp_1198_;
}
else
{
lean_object* v_cls_1236_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_cls_1236_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4));
v___x_1257_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
v___x_1258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1229_, v_opts_1234_, v___x_1257_);
lean_dec_ref(v_opts_1234_);
lean_dec(v___x_1229_);
if (v___x_1258_ == 0)
{
lean_dec(v_hint_1184_);
lean_dec(v_mod_1182_);
v___y_1199_ = v___y_1186_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1259_; lean_object* v___y_1261_; 
v___x_1259_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
if (v_isExporting_1190_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__18));
v___y_1261_ = v___x_1268_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__19));
v___y_1261_ = v___x_1269_;
goto v___jp_1260_;
}
v___jp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_inc_ref(v___y_1261_);
v___x_1262_ = l_Lean_stringToMessageData(v___y_1261_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1259_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
if (v_isMeta_1183_ == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1243_ = v___x_1265_;
v___y_1244_ = v___x_1266_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1267_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1243_ = v___x_1265_;
v___y_1244_ = v___x_1267_;
goto v___jp_1242_;
}
}
}
v___jp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1238_);
lean_ctor_set(v___x_1240_, 1, v___y_1239_);
v___x_1241_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1236_, v___x_1240_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_dec_ref_known(v___x_1241_, 1);
v___y_1199_ = v___y_1186_;
goto v___jp_1198_;
}
else
{
lean_dec_ref_known(v_entry_1194_, 1);
return v___x_1241_;
}
}
v___jp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_inc_ref(v___y_1244_);
v___x_1245_ = l_Lean_stringToMessageData(v___y_1244_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___y_1243_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = l_Lean_MessageData_ofName(v_mod_1182_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_Name_isAnonymous(v_hint_1184_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8);
v___x_1253_ = l_Lean_MessageData_ofName(v_hint_1184_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___y_1238_ = v___x_1250_;
v___y_1239_ = v___x_1254_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_hint_1184_);
v___x_1255_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
v___y_1238_ = v___x_1250_;
v___y_1239_ = v___x_1256_;
goto v___jp_1237_;
}
}
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref_known(v_entry_1194_, 1);
lean_dec(v_hint_1184_);
lean_dec(v_mod_1182_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
v___jp_1198_:
{
lean_object* v___x_1200_; lean_object* v_toEnvExtension_1201_; lean_object* v_env_1202_; lean_object* v_messages_1203_; lean_object* v_scopes_1204_; lean_object* v_usedQuotCtxts_1205_; lean_object* v_nextMacroScope_1206_; lean_object* v_maxRecDepth_1207_; lean_object* v_ngen_1208_; lean_object* v_auxDeclNGen_1209_; lean_object* v_infoState_1210_; lean_object* v_traceState_1211_; lean_object* v_snapshotTasks_1212_; lean_object* v_prevLinterStates_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1225_; 
v___x_1200_ = lean_st_ref_take(v___y_1199_);
v_toEnvExtension_1201_ = lean_ctor_get(v___x_1195_, 0);
v_env_1202_ = lean_ctor_get(v___x_1200_, 0);
v_messages_1203_ = lean_ctor_get(v___x_1200_, 1);
v_scopes_1204_ = lean_ctor_get(v___x_1200_, 2);
v_usedQuotCtxts_1205_ = lean_ctor_get(v___x_1200_, 3);
v_nextMacroScope_1206_ = lean_ctor_get(v___x_1200_, 4);
v_maxRecDepth_1207_ = lean_ctor_get(v___x_1200_, 5);
v_ngen_1208_ = lean_ctor_get(v___x_1200_, 6);
v_auxDeclNGen_1209_ = lean_ctor_get(v___x_1200_, 7);
v_infoState_1210_ = lean_ctor_get(v___x_1200_, 8);
v_traceState_1211_ = lean_ctor_get(v___x_1200_, 9);
v_snapshotTasks_1212_ = lean_ctor_get(v___x_1200_, 10);
v_prevLinterStates_1213_ = lean_ctor_get(v___x_1200_, 11);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1215_ = v___x_1200_;
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_prevLinterStates_1213_);
lean_inc(v_snapshotTasks_1212_);
lean_inc(v_traceState_1211_);
lean_inc(v_infoState_1210_);
lean_inc(v_auxDeclNGen_1209_);
lean_inc(v_ngen_1208_);
lean_inc(v_maxRecDepth_1207_);
lean_inc(v_nextMacroScope_1206_);
lean_inc(v_usedQuotCtxts_1205_);
lean_inc(v_scopes_1204_);
lean_inc(v_messages_1203_);
lean_inc(v_env_1202_);
lean_dec(v___x_1200_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_asyncMode_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v_asyncMode_1217_ = lean_ctor_get(v_toEnvExtension_1201_, 2);
v___x_1218_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1195_, v_env_1202_, v_entry_1194_, v_asyncMode_1217_, v___x_1197_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_messages_1203_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_scopes_1204_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_usedQuotCtxts_1205_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_nextMacroScope_1206_);
lean_ctor_set(v_reuseFailAlloc_1224_, 5, v_maxRecDepth_1207_);
lean_ctor_set(v_reuseFailAlloc_1224_, 6, v_ngen_1208_);
lean_ctor_set(v_reuseFailAlloc_1224_, 7, v_auxDeclNGen_1209_);
lean_ctor_set(v_reuseFailAlloc_1224_, 8, v_infoState_1210_);
lean_ctor_set(v_reuseFailAlloc_1224_, 9, v_traceState_1211_);
lean_ctor_set(v_reuseFailAlloc_1224_, 10, v_snapshotTasks_1212_);
lean_ctor_set(v_reuseFailAlloc_1224_, 11, v_prevLinterStates_1213_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_st_ref_put(v___y_1199_, v___x_1220_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1272_, lean_object* v_isMeta_1273_, lean_object* v_hint_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v_isMeta_boxed_1278_; lean_object* v_res_1279_; 
v_isMeta_boxed_1278_ = lean_unbox(v_isMeta_1273_);
v_res_1279_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1272_, v_isMeta_boxed_1278_, v_hint_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1280_, lean_object* v_declName_1281_, lean_object* v_as_1282_, size_t v_sz_1283_, size_t v_i_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_usize_dec_lt(v_i_1284_, v_sz_1283_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_declName_1281_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_b_1285_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v_modules_1292_; lean_object* v___x_1293_; lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v_toImport_1296_; lean_object* v_module_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1291_ = l_Lean_Environment_header(v___x_1280_);
v_modules_1292_ = lean_ctor_get(v___x_1291_, 3);
lean_inc_ref(v_modules_1292_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1294_ = lean_array_uget_borrowed(v_as_1282_, v_i_1284_);
v___x_1295_ = lean_array_get(v___x_1293_, v_modules_1292_, v_a_1294_);
lean_dec_ref(v_modules_1292_);
v_toImport_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_ref(v_toImport_1296_);
lean_dec(v___x_1295_);
v_module_1297_ = lean_ctor_get(v_toImport_1296_, 0);
lean_inc(v_module_1297_);
lean_dec_ref(v_toImport_1296_);
v___x_1298_ = 0;
lean_inc(v_declName_1281_);
v___x_1299_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1297_, v___x_1298_, v_declName_1281_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; 
lean_dec_ref_known(v___x_1299_, 1);
v___x_1300_ = lean_box(0);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1284_, v___x_1301_);
v_i_1284_ = v___x_1302_;
v_b_1285_ = v___x_1300_;
goto _start;
}
else
{
lean_dec(v_declName_1281_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1304_, lean_object* v_declName_1305_, lean_object* v_as_1306_, lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
size_t v_sz_boxed_1313_; size_t v_i_boxed_1314_; lean_object* v_res_1315_; 
v_sz_boxed_1313_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1314_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1304_, v_declName_1305_, v_as_1306_, v_sz_boxed_1313_, v_i_boxed_1314_, v_b_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v_as_1306_);
lean_dec_ref(v___x_1304_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1316_, lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
else
{
lean_object* v_key_1319_; lean_object* v_value_1320_; lean_object* v_tail_1321_; uint8_t v___x_1322_; 
v_key_1319_ = lean_ctor_get(v_x_1317_, 0);
v_value_1320_ = lean_ctor_get(v_x_1317_, 1);
v_tail_1321_ = lean_ctor_get(v_x_1317_, 2);
v___x_1322_ = lean_name_eq(v_key_1319_, v_a_1316_);
if (v___x_1322_ == 0)
{
v_x_1317_ = v_tail_1321_;
goto _start;
}
else
{
lean_object* v___x_1324_; 
lean_inc(v_value_1320_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_value_1320_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1325_, v_x_1326_);
lean_dec(v_x_1326_);
lean_dec(v_a_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_buckets_1330_; lean_object* v___x_1331_; uint64_t v___y_1333_; 
v_buckets_1330_ = lean_ctor_get(v_m_1328_, 1);
v___x_1331_ = lean_array_get_size(v_buckets_1330_);
if (lean_obj_tag(v_a_1329_) == 0)
{
uint64_t v___x_1347_; 
v___x_1347_ = 1723ULL;
v___y_1333_ = v___x_1347_;
goto v___jp_1332_;
}
else
{
uint64_t v_hash_1348_; 
v_hash_1348_ = lean_ctor_get_uint64(v_a_1329_, sizeof(void*)*2);
v___y_1333_ = v_hash_1348_;
goto v___jp_1332_;
}
v___jp_1332_:
{
uint64_t v___x_1334_; uint64_t v___x_1335_; uint64_t v_fold_1336_; uint64_t v___x_1337_; uint64_t v___x_1338_; uint64_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1334_ = 32ULL;
v___x_1335_ = lean_uint64_shift_right(v___y_1333_, v___x_1334_);
v_fold_1336_ = lean_uint64_xor(v___y_1333_, v___x_1335_);
v___x_1337_ = 16ULL;
v___x_1338_ = lean_uint64_shift_right(v_fold_1336_, v___x_1337_);
v___x_1339_ = lean_uint64_xor(v_fold_1336_, v___x_1338_);
v___x_1340_ = lean_uint64_to_usize(v___x_1339_);
v___x_1341_ = lean_usize_of_nat(v___x_1331_);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_sub(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_usize_land(v___x_1340_, v___x_1343_);
v___x_1345_ = lean_array_uget_borrowed(v_buckets_1330_, v___x_1344_);
v___x_1346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1329_, v___x_1345_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1349_, v_a_1350_);
lean_dec(v_a_1350_);
lean_dec_ref(v_m_1349_);
return v_res_1351_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___x_1355_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0));
v___x_1356_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1355_, v___x_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1359_, uint8_t v_isMeta_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_env_1368_; lean_object* v___y_1370_; lean_object* v___x_1383_; 
v___x_1364_ = lean_st_ref_get(v___y_1362_);
v_env_1368_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_ref(v_env_1368_);
lean_dec(v___x_1364_);
v___x_1383_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1368_, v_declName_1359_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_dec_ref(v_env_1368_);
lean_dec(v_declName_1359_);
goto v___jp_1365_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1385_; lean_object* v_modules_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_val_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_Environment_header(v_env_1368_);
v_modules_1386_ = lean_ctor_get(v___x_1385_, 3);
lean_inc_ref(v_modules_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = lean_array_get_size(v_modules_1386_);
v___x_1388_ = lean_nat_dec_lt(v_val_1384_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v_modules_1386_);
lean_dec(v_val_1384_);
lean_dec_ref(v_env_1368_);
lean_dec(v_declName_1359_);
goto v___jp_1365_;
}
else
{
lean_object* v___x_1389_; lean_object* v_env_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___y_1394_; 
v___x_1389_ = lean_st_ref_get(v___y_1362_);
v_env_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc_ref(v_env_1390_);
lean_dec(v___x_1389_);
v___x_1391_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__2);
v___x_1392_ = lean_array_fget(v_modules_1386_, v_val_1384_);
lean_dec(v_val_1384_);
lean_dec_ref(v_modules_1386_);
if (v_isMeta_1360_ == 0)
{
lean_dec_ref(v_env_1390_);
v___y_1394_ = v_isMeta_1360_;
goto v___jp_1393_;
}
else
{
uint8_t v___x_1405_; 
lean_inc(v_declName_1359_);
v___x_1405_ = l_Lean_isMarkedMeta(v_env_1390_, v_declName_1359_);
if (v___x_1405_ == 0)
{
v___y_1394_ = v_isMeta_1360_;
goto v___jp_1393_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = 0;
v___y_1394_ = v___x_1406_;
goto v___jp_1393_;
}
}
v___jp_1393_:
{
lean_object* v_toImport_1395_; lean_object* v_module_1396_; lean_object* v___x_1397_; 
v_toImport_1395_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_toImport_1395_);
lean_dec(v___x_1392_);
v_module_1396_ = lean_ctor_get(v_toImport_1395_, 0);
lean_inc(v_module_1396_);
lean_dec_ref(v_toImport_1395_);
lean_inc(v_declName_1359_);
v___x_1397_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1396_, v___y_1394_, v_declName_1359_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref_known(v___x_1397_, 1);
v___x_1398_ = l_Lean_indirectModUseExt;
v___x_1399_ = lean_box(1);
v___x_1400_ = lean_box(0);
lean_inc_ref(v_env_1368_);
v___x_1401_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1391_, v___x_1398_, v_env_1368_, v___x_1399_, v___x_1400_);
v___x_1402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1401_, v_declName_1359_);
lean_dec(v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__3));
v___y_1370_ = v___x_1403_;
goto v___jp_1369_;
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v___x_1402_, 1);
v___y_1370_ = v_val_1404_;
goto v___jp_1369_;
}
}
else
{
lean_dec_ref(v_env_1368_);
lean_dec(v_declName_1359_);
return v___x_1397_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
v___jp_1369_:
{
lean_object* v___x_1371_; size_t v_sz_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_box(0);
v_sz_1372_ = lean_array_size(v___y_1370_);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1368_, v_declName_1359_, v___y_1370_, v_sz_1372_, v___x_1373_, v___x_1371_, v___y_1361_, v___y_1362_);
lean_dec_ref(v___y_1370_);
lean_dec_ref(v_env_1368_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v___x_1374_, 0);
lean_dec(v_unused_1382_);
v___x_1376_ = v___x_1374_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v___x_1374_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1371_);
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1371_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1407_, lean_object* v_isMeta_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_isMeta_boxed_1412_; lean_object* v_res_1413_; 
v_isMeta_boxed_1412_ = lean_unbox(v_isMeta_1408_);
v_res_1413_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1407_, v_isMeta_boxed_1412_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
if (lean_obj_tag(v_as_x27_1414_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_b_1415_);
return v___x_1419_;
}
else
{
lean_object* v_head_1420_; lean_object* v_tail_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v_head_1420_ = lean_ctor_get(v_as_x27_1414_, 0);
v_tail_1421_ = lean_ctor_get(v_as_x27_1414_, 1);
v___x_1422_ = 1;
lean_inc(v_head_1420_);
v___x_1423_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1420_, v___x_1422_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref_known(v___x_1423_, 1);
v___x_1424_ = lean_box(0);
v_as_x27_1414_ = v_tail_1421_;
v_b_1415_ = v___x_1424_;
goto _start;
}
else
{
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1426_, lean_object* v_b_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1426_, v_b_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v_as_x27_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1432_, lean_object* v_opts_1433_, lean_object* v_currNamespace_1434_, lean_object* v_openDecls_1435_, lean_object* v_n_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = l_Lean_ResolveName_resolveGlobalName(v_env_1432_, v_opts_1433_, v_currNamespace_1434_, v_openDecls_1435_, v_n_1436_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v___y_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1441_, lean_object* v_opts_1442_, lean_object* v_currNamespace_1443_, lean_object* v_openDecls_1444_, lean_object* v_n_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1441_, v_opts_1442_, v_currNamespace_1443_, v_openDecls_1444_, v_n_1445_, v___y_1446_, v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v_opts_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Elab_Command_getRef___redArg(v___y_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_fileName_1456_; lean_object* v_fileMap_1457_; lean_object* v_currRecDepth_1458_; lean_object* v_cmdPos_1459_; lean_object* v_macroStack_1460_; lean_object* v_quotContext_x3f_1461_; lean_object* v_currMacroScope_1462_; lean_object* v_snap_x3f_1463_; lean_object* v_cancelTk_x3f_1464_; uint8_t v_suppressElabErrors_1465_; lean_object* v_ref_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v_fileName_1456_ = lean_ctor_get(v___y_1451_, 0);
v_fileMap_1457_ = lean_ctor_get(v___y_1451_, 1);
v_currRecDepth_1458_ = lean_ctor_get(v___y_1451_, 2);
v_cmdPos_1459_ = lean_ctor_get(v___y_1451_, 3);
v_macroStack_1460_ = lean_ctor_get(v___y_1451_, 4);
v_quotContext_x3f_1461_ = lean_ctor_get(v___y_1451_, 5);
v_currMacroScope_1462_ = lean_ctor_get(v___y_1451_, 6);
v_snap_x3f_1463_ = lean_ctor_get(v___y_1451_, 8);
v_cancelTk_x3f_1464_ = lean_ctor_get(v___y_1451_, 9);
v_suppressElabErrors_1465_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*10);
v_ref_1466_ = l_Lean_replaceRef(v_ref_1449_, v_a_1455_);
lean_dec(v_a_1455_);
lean_inc(v_cancelTk_x3f_1464_);
lean_inc(v_snap_x3f_1463_);
lean_inc(v_currMacroScope_1462_);
lean_inc(v_quotContext_x3f_1461_);
lean_inc(v_macroStack_1460_);
lean_inc(v_cmdPos_1459_);
lean_inc(v_currRecDepth_1458_);
lean_inc_ref(v_fileMap_1457_);
lean_inc_ref(v_fileName_1456_);
v___x_1467_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1467_, 0, v_fileName_1456_);
lean_ctor_set(v___x_1467_, 1, v_fileMap_1457_);
lean_ctor_set(v___x_1467_, 2, v_currRecDepth_1458_);
lean_ctor_set(v___x_1467_, 3, v_cmdPos_1459_);
lean_ctor_set(v___x_1467_, 4, v_macroStack_1460_);
lean_ctor_set(v___x_1467_, 5, v_quotContext_x3f_1461_);
lean_ctor_set(v___x_1467_, 6, v_currMacroScope_1462_);
lean_ctor_set(v___x_1467_, 7, v_ref_1466_);
lean_ctor_set(v___x_1467_, 8, v_snap_x3f_1463_);
lean_ctor_set(v___x_1467_, 9, v_cancelTk_x3f_1464_);
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*10, v_suppressElabErrors_1465_);
v___x_1468_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1450_, v___x_1467_, v___y_1452_);
lean_dec_ref_known(v___x_1467_, 10);
return v___x_1468_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_msg_1450_);
v_a_1469_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1454_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1454_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1477_, v_msg_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v_ref_1477_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1483_, lean_object* v_currNamespace_1484_, lean_object* v_openDecls_1485_, lean_object* v_n_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = l_Lean_ResolveName_resolveNamespace(v_env_1483_, v_currNamespace_1484_, v_openDecls_1485_, v_n_1486_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v___y_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1491_, lean_object* v_currNamespace_1492_, lean_object* v_openDecls_1493_, lean_object* v_n_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1491_, v_currNamespace_1492_, v_openDecls_1493_, v_n_1494_, v___y_1495_, v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_currNamespace_1498_);
lean_ctor_set(v___x_1501_, 1, v___y_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1502_, v___y_1503_, v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1506_, lean_object* v___y_1507_){
_start:
{
if (lean_obj_tag(v_x_1506_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v_x_1506_, 0);
lean_inc(v_a_1508_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_a_1508_);
lean_ctor_set(v___x_1509_, 1, v___y_1507_);
return v___x_1509_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v_x_1506_, 0);
lean_inc(v_a_1510_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_a_1510_);
lean_ctor_set(v___x_1511_, 1, v___y_1507_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1512_, v___y_1513_);
lean_dec_ref(v_x_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1515_, lean_object* v_stx_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1515_, v_stx_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
if (lean_obj_tag(v_a_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1529_; 
v_a_1521_ = lean_ctor_get(v___x_1519_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1530_);
v___x_1523_ = v___x_1519_;
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = lean_box(0);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1525_);
v___x_1527_ = v___x_1523_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_a_1521_);
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
lean_object* v_val_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1559_; 
v_val_1531_ = lean_ctor_get(v_a_1520_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1520_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1533_ = v_a_1520_;
v_isShared_1534_ = v_isSharedCheck_1559_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_val_1531_);
lean_dec(v_a_1520_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1559_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_snd_1535_; 
v_snd_1535_ = lean_ctor_get(v_val_1531_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_val_1531_);
if (lean_obj_tag(v_snd_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1533_);
v_a_1536_ = lean_ctor_get(v___x_1519_, 1);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1519_, 2);
v_a_1537_ = lean_ctor_get(v_snd_1535_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_snd_1535_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v_snd_1535_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v_snd_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1542_, v_a_1536_);
lean_dec_ref(v___x_1542_);
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1558_; 
v_a_1546_ = lean_ctor_get(v___x_1519_, 1);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1519_, 2);
v_a_1547_ = lean_ctor_get(v_snd_1535_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_snd_1535_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1549_ = v_snd_1535_;
v_isShared_1550_ = v_isSharedCheck_1558_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v_snd_1535_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1558_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_a_1547_);
v___x_1552_ = v___x_1533_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1554_, v_a_1546_);
lean_dec_ref(v___x_1554_);
return v___x_1555_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1560_ = lean_ctor_get(v___x_1519_, 0);
v_a_1561_ = lean_ctor_get(v___x_1519_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1519_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_inc(v_a_1560_);
lean_dec(v___x_1519_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1569_, lean_object* v_stx_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1569_, v_stx_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1573_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
if (lean_obj_tag(v_as_1582_) == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
else
{
lean_object* v_head_1588_; lean_object* v_tail_1589_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_scopes_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_opts_1598_; uint8_t v_hasTrace_1599_; 
v_head_1588_ = lean_ctor_get(v_as_1582_, 0);
lean_inc(v_head_1588_);
v_tail_1589_ = lean_ctor_get(v_as_1582_, 1);
lean_inc(v_tail_1589_);
lean_dec_ref_known(v_as_1582_, 2);
v_fst_1590_ = lean_ctor_get(v_head_1588_, 0);
lean_inc(v_fst_1590_);
v_snd_1591_ = lean_ctor_get(v_head_1588_, 1);
lean_inc(v_snd_1591_);
lean_dec(v_head_1588_);
v___x_1592_ = l_Lean_inheritedTraceOptions;
v___x_1593_ = lean_st_ref_get(v___x_1592_);
v___x_1594_ = lean_st_ref_get(v___y_1584_);
v_scopes_1595_ = lean_ctor_get(v___x_1594_, 2);
lean_inc(v_scopes_1595_);
lean_dec(v___x_1594_);
v___x_1596_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1597_ = l_List_head_x21___redArg(v___x_1596_, v_scopes_1595_);
lean_dec(v_scopes_1595_);
v_opts_1598_ = lean_ctor_get(v___x_1597_, 1);
lean_inc_ref(v_opts_1598_);
lean_dec(v___x_1597_);
v_hasTrace_1599_ = lean_ctor_get_uint8(v_opts_1598_, sizeof(void*)*1);
if (v_hasTrace_1599_ == 0)
{
lean_dec_ref(v_opts_1598_);
lean_dec(v___x_1593_);
lean_dec(v_snd_1591_);
lean_dec(v_fst_1590_);
v_as_1582_ = v_tail_1589_;
goto _start;
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
lean_inc(v_fst_1590_);
v___x_1602_ = l_Lean_Name_append(v___x_1601_, v_fst_1590_);
v___x_1603_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1593_, v_opts_1598_, v___x_1602_);
lean_dec(v___x_1602_);
lean_dec_ref(v_opts_1598_);
lean_dec(v___x_1593_);
if (v___x_1603_ == 0)
{
lean_dec(v_snd_1591_);
lean_dec(v_fst_1590_);
v_as_1582_ = v_tail_1589_;
goto _start;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_snd_1591_);
v___x_1606_ = l_Lean_MessageData_ofFormat(v___x_1605_);
v___x_1607_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1590_, v___x_1606_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref_known(v___x_1607_, 1);
v_as_1582_ = v_tail_1589_;
goto _start;
}
else
{
lean_dec(v_tail_1589_);
return v___x_1607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v_env_1620_; lean_object* v___x_1621_; lean_object* v_scopes_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_opts_1625_; lean_object* v___x_1626_; 
v___x_1619_ = lean_st_ref_get(v___y_1617_);
v_env_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc_ref(v_env_1620_);
lean_dec(v___x_1619_);
v___x_1621_ = lean_st_ref_get(v___y_1617_);
v_scopes_1622_ = lean_ctor_get(v___x_1621_, 2);
lean_inc(v_scopes_1622_);
lean_dec(v___x_1621_);
v___x_1623_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1624_ = l_List_head_x21___redArg(v___x_1623_, v_scopes_1622_);
lean_dec(v_scopes_1622_);
v_opts_1625_ = lean_ctor_get(v___x_1624_, 1);
lean_inc_ref(v_opts_1625_);
lean_dec(v___x_1624_);
v___x_1626_ = l_Lean_Elab_Command_getScope___redArg(v___y_1617_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_currNamespace_1628_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v_currNamespace_1628_ = lean_ctor_get(v_a_1627_, 2);
lean_inc(v_currNamespace_1628_);
lean_dec(v_a_1627_);
v___x_1629_ = l_Lean_Elab_Command_getScope___redArg(v___y_1617_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v_openDecls_1631_; lean_object* v___x_1632_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v_openDecls_1631_ = lean_ctor_get(v_a_1630_, 3);
lean_inc(v_openDecls_1631_);
lean_dec(v_a_1630_);
v___x_1632_ = l_Lean_Elab_Command_getRef___redArg(v___y_1616_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1616_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_currRecDepth_1636_; lean_object* v_quotContext_x3f_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v_methods_1643_; lean_object* v_a_1645_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v_currRecDepth_1636_ = lean_ctor_get(v___y_1616_, 2);
v_quotContext_x3f_1637_ = lean_ctor_get(v___y_1616_, 5);
lean_inc_ref_n(v_env_1620_, 3);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1638_, 0, v_env_1620_);
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1639_, 0, v_env_1620_);
lean_inc_n(v_currNamespace_1628_, 2);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1640_, 0, v_currNamespace_1628_);
lean_inc(v_openDecls_1631_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1641_, 0, v_env_1620_);
lean_closure_set(v___f_1641_, 1, v_currNamespace_1628_);
lean_closure_set(v___f_1641_, 2, v_openDecls_1631_);
v___f_1642_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1642_, 0, v_env_1620_);
lean_closure_set(v___f_1642_, 1, v_opts_1625_);
lean_closure_set(v___f_1642_, 2, v_currNamespace_1628_);
lean_closure_set(v___f_1642_, 3, v_openDecls_1631_);
v_methods_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1643_, 0, v___f_1639_);
lean_ctor_set(v_methods_1643_, 1, v___f_1640_);
lean_ctor_set(v_methods_1643_, 2, v___f_1638_);
lean_ctor_set(v_methods_1643_, 3, v___f_1641_);
lean_ctor_set(v_methods_1643_, 4, v___f_1642_);
if (lean_obj_tag(v_quotContext_x3f_1637_) == 0)
{
lean_object* v___x_1718_; lean_object* v_a_1719_; 
v___x_1718_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1617_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v_a_1645_ = v_a_1719_;
goto v___jp_1644_;
}
else
{
lean_object* v_val_1720_; 
v_val_1720_ = lean_ctor_get(v_quotContext_x3f_1637_, 0);
lean_inc(v_val_1720_);
v_a_1645_ = v_val_1720_;
goto v___jp_1644_;
}
v___jp_1644_:
{
lean_object* v___x_1646_; lean_object* v_maxRecDepth_1647_; lean_object* v___x_1648_; lean_object* v_nextMacroScope_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1646_ = lean_st_ref_get(v___y_1617_);
v_maxRecDepth_1647_ = lean_ctor_get(v___x_1646_, 5);
lean_inc(v_maxRecDepth_1647_);
lean_dec(v___x_1646_);
v___x_1648_ = lean_st_ref_get(v___y_1617_);
v_nextMacroScope_1649_ = lean_ctor_get(v___x_1648_, 4);
lean_inc(v_nextMacroScope_1649_);
lean_dec(v___x_1648_);
lean_inc(v_currRecDepth_1636_);
v___x_1650_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1650_, 0, v_methods_1643_);
lean_ctor_set(v___x_1650_, 1, v_a_1645_);
lean_ctor_set(v___x_1650_, 2, v_a_1635_);
lean_ctor_set(v___x_1650_, 3, v_currRecDepth_1636_);
lean_ctor_set(v___x_1650_, 4, v_maxRecDepth_1647_);
lean_ctor_set(v___x_1650_, 5, v_a_1633_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1652_, 0, v_nextMacroScope_1649_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_ctor_set(v___x_1652_, 2, v___x_1651_);
v___x_1653_ = lean_apply_2(v_x_1615_, v___x_1650_, v___x_1652_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v_a_1655_; lean_object* v_macroScope_1656_; lean_object* v_traceMsgs_1657_; lean_object* v_expandedMacroDecls_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 1);
lean_inc(v_a_1654_);
v_a_1655_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1653_, 2);
v_macroScope_1656_ = lean_ctor_get(v_a_1654_, 0);
lean_inc(v_macroScope_1656_);
v_traceMsgs_1657_ = lean_ctor_get(v_a_1654_, 1);
lean_inc(v_traceMsgs_1657_);
v_expandedMacroDecls_1658_ = lean_ctor_get(v_a_1654_, 2);
lean_inc(v_expandedMacroDecls_1658_);
lean_dec(v_a_1654_);
v___x_1659_ = lean_box(0);
v___x_1660_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1658_, v___x_1659_, v___y_1616_, v___y_1617_);
lean_dec(v_expandedMacroDecls_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; lean_object* v_env_1662_; lean_object* v_messages_1663_; lean_object* v_scopes_1664_; lean_object* v_usedQuotCtxts_1665_; lean_object* v_maxRecDepth_1666_; lean_object* v_ngen_1667_; lean_object* v_auxDeclNGen_1668_; lean_object* v_infoState_1669_; lean_object* v_traceState_1670_; lean_object* v_snapshotTasks_1671_; lean_object* v_prevLinterStates_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1698_; 
lean_dec_ref_known(v___x_1660_, 1);
v___x_1661_ = lean_st_ref_take(v___y_1617_);
v_env_1662_ = lean_ctor_get(v___x_1661_, 0);
v_messages_1663_ = lean_ctor_get(v___x_1661_, 1);
v_scopes_1664_ = lean_ctor_get(v___x_1661_, 2);
v_usedQuotCtxts_1665_ = lean_ctor_get(v___x_1661_, 3);
v_maxRecDepth_1666_ = lean_ctor_get(v___x_1661_, 5);
v_ngen_1667_ = lean_ctor_get(v___x_1661_, 6);
v_auxDeclNGen_1668_ = lean_ctor_get(v___x_1661_, 7);
v_infoState_1669_ = lean_ctor_get(v___x_1661_, 8);
v_traceState_1670_ = lean_ctor_get(v___x_1661_, 9);
v_snapshotTasks_1671_ = lean_ctor_get(v___x_1661_, 10);
v_prevLinterStates_1672_ = lean_ctor_get(v___x_1661_, 11);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v___x_1661_, 4);
lean_dec(v_unused_1699_);
v___x_1674_ = v___x_1661_;
v_isShared_1675_ = v_isSharedCheck_1698_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_prevLinterStates_1672_);
lean_inc(v_snapshotTasks_1671_);
lean_inc(v_traceState_1670_);
lean_inc(v_infoState_1669_);
lean_inc(v_auxDeclNGen_1668_);
lean_inc(v_ngen_1667_);
lean_inc(v_maxRecDepth_1666_);
lean_inc(v_usedQuotCtxts_1665_);
lean_inc(v_scopes_1664_);
lean_inc(v_messages_1663_);
lean_inc(v_env_1662_);
lean_dec(v___x_1661_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1698_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_macroScope_1656_);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_env_1662_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_messages_1663_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_scopes_1664_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_usedQuotCtxts_1665_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_macroScope_1656_);
lean_ctor_set(v_reuseFailAlloc_1697_, 5, v_maxRecDepth_1666_);
lean_ctor_set(v_reuseFailAlloc_1697_, 6, v_ngen_1667_);
lean_ctor_set(v_reuseFailAlloc_1697_, 7, v_auxDeclNGen_1668_);
lean_ctor_set(v_reuseFailAlloc_1697_, 8, v_infoState_1669_);
lean_ctor_set(v_reuseFailAlloc_1697_, 9, v_traceState_1670_);
lean_ctor_set(v_reuseFailAlloc_1697_, 10, v_snapshotTasks_1671_);
lean_ctor_set(v_reuseFailAlloc_1697_, 11, v_prevLinterStates_1672_);
v___x_1677_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = lean_st_ref_put(v___y_1617_, v___x_1677_);
v___x_1679_ = l_List_reverse___redArg(v_traceMsgs_1657_);
v___x_1680_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1679_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v___x_1680_, 0);
lean_dec(v_unused_1688_);
v___x_1682_ = v___x_1680_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_dec(v___x_1680_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v_a_1655_);
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1655_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_a_1655_);
v_a_1689_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1680_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1680_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_traceMsgs_1657_);
lean_dec(v_macroScope_1656_);
lean_dec(v_a_1655_);
v_a_1700_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1660_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1660_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1653_, 2);
if (lean_obj_tag(v_a_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_a_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_a_1709_ = lean_ctor_get(v_a_1708_, 0);
lean_inc(v_a_1709_);
v_a_1710_ = lean_ctor_get(v_a_1708_, 1);
lean_inc_ref(v_a_1710_);
lean_dec_ref_known(v_a_1708_, 2);
v___x_1711_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1712_ = lean_string_dec_eq(v_a_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_a_1710_);
v___x_1714_ = l_Lean_MessageData_ofFormat(v___x_1713_);
v___x_1715_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1709_, v___x_1714_, v___y_1616_, v___y_1617_);
lean_dec(v_a_1709_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; 
lean_dec_ref(v_a_1710_);
v___x_1716_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1709_);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_a_1633_);
lean_dec(v_openDecls_1631_);
lean_dec(v_currNamespace_1628_);
lean_dec_ref(v_opts_1625_);
lean_dec_ref(v_env_1620_);
lean_dec_ref(v_x_1615_);
v_a_1721_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1634_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1634_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_openDecls_1631_);
lean_dec(v_currNamespace_1628_);
lean_dec_ref(v_opts_1625_);
lean_dec_ref(v_env_1620_);
lean_dec_ref(v_x_1615_);
v_a_1729_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1632_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1632_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_currNamespace_1628_);
lean_dec_ref(v_opts_1625_);
lean_dec_ref(v_env_1620_);
lean_dec_ref(v_x_1615_);
v_a_1737_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1629_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1629_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_opts_1625_);
lean_dec_ref(v_env_1620_);
lean_dec_ref(v_x_1615_);
v_a_1745_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1626_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1626_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1757_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1772_ = l_String_toRawSubstring_x27(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1796_ = lean_unsigned_to_nat(14u);
v___x_1797_ = lean_unsigned_to_nat(22u);
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1799_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1800_ = l_mkPanicMessageWithDecl(v___x_1799_, v___x_1798_, v___x_1797_, v___x_1796_, v___x_1795_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1817_ = l_String_toRawSubstring_x27(v___x_1816_);
return v___x_1817_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1830_ = l_Lean_mkAtom(v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1833_ = l_Lean_mkAtom(v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1834_, lean_object* v_id_1835_, lean_object* v_stx_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_pat_1841_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1836_);
v___x_1845_ = l_Lean_Syntax_isOfKind(v_stx_1836_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1836_);
v___x_1847_ = l_Lean_Syntax_isOfKind(v_stx_1836_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v_a_1854_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v_a_1888_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v_a_1922_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v_a_1958_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v_a_1992_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v_a_2026_; uint8_t v___x_2057_; 
v___x_1848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1836_);
v___x_2057_ = l_Lean_Syntax_isOfKind(v_stx_1836_, v___x_1848_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1836_);
v___x_2059_ = l_Lean_Syntax_isOfKind(v_stx_1836_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1836_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_stx_1836_, v___x_2060_);
if (v___x_2061_ == 0)
{
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v_quotContext_x3f_2066_; lean_object* v___x_2067_; lean_object* v_a_2069_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v_quotContext_x3f_2066_ = lean_ctor_get(v_a_1837_, 5);
v___x_2067_ = l_Lean_SourceInfo_fromRef(v_a_2063_, v___x_2061_);
lean_dec(v_a_2063_);
if (lean_obj_tag(v_quotContext_x3f_2066_) == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v_a_2069_ = v_a_2101_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v___x_2067_);
lean_dec(v_a_2065_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2102_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2100_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_val_2110_; 
v_val_2110_ = lean_ctor_get(v_quotContext_x3f_2066_, 0);
lean_inc(v_val_2110_);
v_a_2069_ = v_val_2110_;
goto v___jp_2068_;
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2070_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2072_ = l_Lean_addMacroScope(v_a_2069_, v___x_2071_, v_a_2065_);
v___x_2073_ = lean_box(0);
lean_inc_n(v___x_2067_, 3);
v___x_2074_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2067_);
lean_ctor_set(v___x_2074_, 1, v___x_2070_);
lean_ctor_set(v___x_2074_, 2, v___x_2072_);
lean_ctor_set(v___x_2074_, 3, v___x_2073_);
v___x_2075_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2067_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2078_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2077_, v_stx_1836_);
v___x_2079_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2091_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2091_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2091_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2084_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2067_);
v___x_2085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2067_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l_Lean_Syntax_node4(v___x_2067_, v___x_1848_, v___x_2074_, v___x_2076_, v___x_2078_, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v_a_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2087_);
v___x_2089_ = v___x_2082_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v___x_2078_);
lean_dec_ref_known(v___x_2076_, 2);
lean_dec_ref_known(v___x_2074_, 4);
lean_dec(v___x_2067_);
v_a_2092_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2079_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2079_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_2063_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2111_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2064_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2064_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2119_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2062_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2062_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2128_; 
lean_dec(v_id_1835_);
v_val_2127_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2128_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2127_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v_pat_1841_ = v_a_2129_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_stx_1836_);
v_a_2130_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2128_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2138_);
lean_inc(v___x_2139_);
v___x_2140_ = l_Lean_Syntax_matchesNull(v___x_2139_, v___x_2138_);
if (v___x_2140_ == 0)
{
lean_dec(v___x_2139_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_quotContext_x3f_2145_; lean_object* v___x_2146_; lean_object* v_a_2148_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v_quotContext_x3f_2145_ = lean_ctor_get(v_a_1837_, 5);
v___x_2146_ = l_Lean_SourceInfo_fromRef(v_a_2142_, v___x_2140_);
lean_dec(v_a_2142_);
if (lean_obj_tag(v_quotContext_x3f_2145_) == 0)
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v_a_2148_ = v_a_2180_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v___x_2146_);
lean_dec(v_a_2144_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2181_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2179_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_val_2189_; 
v_val_2189_ = lean_ctor_get(v_quotContext_x3f_2145_, 0);
lean_inc(v_val_2189_);
v_a_2148_ = v_val_2189_;
goto v___jp_2147_;
}
v___jp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2149_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2150_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2151_ = l_Lean_addMacroScope(v_a_2148_, v___x_2150_, v_a_2144_);
v___x_2152_ = lean_box(0);
lean_inc_n(v___x_2146_, 3);
v___x_2153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2146_);
lean_ctor_set(v___x_2153_, 1, v___x_2149_);
lean_ctor_set(v___x_2153_, 2, v___x_2151_);
lean_ctor_set(v___x_2153_, 3, v___x_2152_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2146_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2157_ = l_Lean_Syntax_node1(v___x_2146_, v___x_2156_, v_stx_1836_);
v___x_2158_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2170_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2146_);
v___x_2164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2146_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node4(v___x_2146_, v___x_1848_, v___x_2153_, v___x_2155_, v___x_2157_, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v_a_2159_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2166_);
v___x_2168_ = v___x_2161_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v___x_2157_);
lean_dec_ref_known(v___x_2155_, 2);
lean_dec_ref_known(v___x_2153_, 4);
lean_dec(v___x_2146_);
v_a_2171_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2158_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2158_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2142_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2190_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2143_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2143_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2198_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2141_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2141_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_val_2206_; lean_object* v___x_2207_; 
lean_dec(v_id_1835_);
v_val_2206_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2207_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2206_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v_pat_1841_ = v_a_2208_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_stx_1836_);
v_a_2209_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2207_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2207_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v___x_2217_; lean_object* v_stx_2218_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2248_; lean_object* v___y_2249_; 
v___x_2217_ = lean_unsigned_to_nat(0u);
v_stx_2218_ = l_Lean_Syntax_getArg(v___x_2139_, v___x_2217_);
lean_dec(v___x_2139_);
v___x_2236_ = lean_unsigned_to_nat(2u);
v___x_2237_ = lean_unsigned_to_nat(3u);
v___x_2238_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2237_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2238_);
v___x_2394_ = l_Lean_Syntax_isOfKind(v___x_2238_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_dec(v___x_2238_);
lean_dec(v_stx_2218_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v_quotContext_x3f_2399_; lean_object* v___x_2400_; lean_object* v_a_2402_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v_quotContext_x3f_2399_ = lean_ctor_get(v_a_1837_, 5);
v___x_2400_ = l_Lean_SourceInfo_fromRef(v_a_2396_, v___x_2059_);
lean_dec(v_a_2396_);
if (lean_obj_tag(v_quotContext_x3f_2399_) == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v_a_2402_ = v_a_2434_;
goto v___jp_2401_;
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v___x_2400_);
lean_dec(v_a_2398_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2435_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2433_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2433_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_val_2443_; 
v_val_2443_ = lean_ctor_get(v_quotContext_x3f_2399_, 0);
lean_inc(v_val_2443_);
v_a_2402_ = v_val_2443_;
goto v___jp_2401_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2403_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2405_ = l_Lean_addMacroScope(v_a_2402_, v___x_2404_, v_a_2398_);
v___x_2406_ = lean_box(0);
lean_inc_n(v___x_2400_, 3);
v___x_2407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2400_);
lean_ctor_set(v___x_2407_, 1, v___x_2403_);
lean_ctor_set(v___x_2407_, 2, v___x_2405_);
lean_ctor_set(v___x_2407_, 3, v___x_2406_);
v___x_2408_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2400_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2411_ = l_Lean_Syntax_node1(v___x_2400_, v___x_2410_, v_stx_1836_);
v___x_2412_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2424_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2424_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2424_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2400_);
v___x_2418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2400_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node4(v___x_2400_, v___x_1848_, v___x_2407_, v___x_2409_, v___x_2411_, v___x_2418_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_a_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2420_);
v___x_2422_ = v___x_2415_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v___x_2411_);
lean_dec_ref_known(v___x_2409_, 2);
lean_dec_ref_known(v___x_2407_, 4);
lean_dec(v___x_2400_);
v_a_2425_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2412_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2412_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_a_2396_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2444_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2397_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2397_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2452_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2395_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2395_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2461_; 
lean_dec(v_id_1835_);
v_val_2460_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2461_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2460_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v_pat_1841_ = v_a_2462_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_stx_1836_);
v_a_2463_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2461_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2461_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
else
{
goto v___jp_2298_;
}
}
else
{
goto v___jp_2298_;
}
v___jp_2219_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2225_ = lean_string_append(v___y_2223_, v___x_2224_);
lean_inc(v___y_2221_);
v___x_2226_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2221_, v_stx_2218_, v_id_1835_, v___x_2225_, v___y_2222_, v___y_2220_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v_pat_1841_ = v_a_2227_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_stx_1836_);
v_a_2228_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
v___jp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2243_ = l_Lean_Syntax_isStrLit_x3f(v___x_2238_);
lean_dec(v___x_2238_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2245_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2244_);
v___y_2220_ = v___y_2241_;
v___y_2221_ = v___x_2242_;
v___y_2222_ = v___y_2240_;
v___y_2223_ = v___x_2245_;
goto v___jp_2219_;
}
else
{
lean_object* v_val_2246_; 
v_val_2246_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v___x_2243_, 1);
v___y_2220_ = v___y_2241_;
v___y_2221_ = v___x_2242_;
v___y_2222_ = v___y_2240_;
v___y_2223_ = v_val_2246_;
goto v___jp_2219_;
}
}
v___jp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(5u);
v___x_2251_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2250_);
v___x_2252_ = l_Lean_Syntax_isNone(v___x_2251_);
if (v___x_2252_ == 0)
{
uint8_t v___x_2253_; 
v___x_2253_ = l_Lean_Syntax_matchesNull(v___x_2251_, v___x_2236_);
if (v___x_2253_ == 0)
{
lean_dec(v___x_2238_);
lean_dec(v_stx_2218_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Elab_Command_getRef___redArg(v___y_2248_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2256_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2256_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2248_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v_quotContext_x3f_2258_; lean_object* v___x_2259_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v_quotContext_x3f_2258_ = lean_ctor_get(v___y_2248_, 5);
v___x_2259_ = l_Lean_SourceInfo_fromRef(v_a_2255_, v___x_2253_);
lean_dec(v_a_2255_);
if (lean_obj_tag(v_quotContext_x3f_2258_) == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2249_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___y_1850_ = v_a_2257_;
v___y_1851_ = v___y_2248_;
v___y_1852_ = v___y_2249_;
v___y_1853_ = v___x_2259_;
v_a_1854_ = v_a_2261_;
goto v___jp_1849_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v___x_2259_);
lean_dec(v_a_2257_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2262_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2260_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2260_);
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
lean_object* v_val_2270_; 
v_val_2270_ = lean_ctor_get(v_quotContext_x3f_2258_, 0);
lean_inc(v_val_2270_);
v___y_1850_ = v_a_2257_;
v___y_1851_ = v___y_2248_;
v___y_1852_ = v___y_2249_;
v___y_1853_ = v___x_2259_;
v_a_1854_ = v_val_2270_;
goto v___jp_1849_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_a_2255_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2271_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2256_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2256_);
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
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2279_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2254_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2254_);
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
else
{
lean_object* v_val_2287_; lean_object* v___x_2288_; 
lean_dec(v_id_1835_);
v_val_2287_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2288_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2287_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v_pat_1841_ = v_a_2289_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_stx_1836_);
v_a_2290_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2288_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2288_);
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
}
else
{
lean_dec(v_id_x3f_1834_);
v___y_2240_ = v___y_2248_;
v___y_2241_ = v___y_2249_;
goto v___jp_2239_;
}
}
else
{
lean_dec(v___x_2251_);
lean_dec(v_id_x3f_1834_);
v___y_2240_ = v___y_2248_;
v___y_2241_ = v___y_2249_;
goto v___jp_2239_;
}
}
v___jp_2298_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2299_ = lean_unsigned_to_nat(4u);
v___x_2300_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2299_);
v___x_2301_ = l_Lean_Syntax_isNone(v___x_2300_);
if (v___x_2301_ == 0)
{
uint8_t v___x_2302_; 
lean_inc(v___x_2300_);
v___x_2302_ = l_Lean_Syntax_matchesNull(v___x_2300_, v___x_2236_);
if (v___x_2302_ == 0)
{
lean_dec(v___x_2300_);
lean_dec(v___x_2238_);
lean_dec(v_stx_2218_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_quotContext_x3f_2307_; lean_object* v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_quotContext_x3f_2307_ = lean_ctor_get(v_a_1837_, 5);
v___x_2308_ = l_Lean_SourceInfo_fromRef(v_a_2304_, v___x_2302_);
lean_dec(v_a_2304_);
if (lean_obj_tag(v_quotContext_x3f_2307_) == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___y_1886_ = v_a_2306_;
v___y_1887_ = v___x_2308_;
v_a_1888_ = v_a_2310_;
goto v___jp_1885_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v___x_2308_);
lean_dec(v_a_2306_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2311_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2309_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2309_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v_val_2319_; 
v_val_2319_ = lean_ctor_get(v_quotContext_x3f_2307_, 0);
lean_inc(v_val_2319_);
v___y_1886_ = v_a_2306_;
v___y_1887_ = v___x_2308_;
v_a_1888_ = v_val_2319_;
goto v___jp_1885_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2304_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2320_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2305_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2305_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2328_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2303_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2303_);
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
lean_object* v_val_2336_; lean_object* v___x_2337_; 
lean_dec(v_id_1835_);
v_val_2336_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2336_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2337_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2336_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_pat_1841_ = v_a_2338_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_stx_1836_);
v_a_2339_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2337_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2337_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
else
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = l_Lean_Syntax_getArg(v___x_2300_, v___x_2138_);
lean_dec(v___x_2300_);
v___x_2348_ = l_Lean_Syntax_matchesNull(v___x_2347_, v___x_2138_);
if (v___x_2348_ == 0)
{
lean_dec(v___x_2238_);
lean_dec(v_stx_2218_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v_quotContext_x3f_2353_; lean_object* v___x_2354_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_quotContext_x3f_2353_ = lean_ctor_get(v_a_1837_, 5);
v___x_2354_ = l_Lean_SourceInfo_fromRef(v_a_2350_, v___x_2348_);
lean_dec(v_a_2350_);
if (lean_obj_tag(v_quotContext_x3f_2353_) == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___y_1920_ = v___x_2354_;
v___y_1921_ = v_a_2352_;
v_a_1922_ = v_a_2356_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v___x_2354_);
lean_dec(v_a_2352_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2357_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2355_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_val_2365_; 
v_val_2365_ = lean_ctor_get(v_quotContext_x3f_2353_, 0);
lean_inc(v_val_2365_);
v___y_1920_ = v___x_2354_;
v___y_1921_ = v_a_2352_;
v_a_1922_ = v_val_2365_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2350_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2366_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2351_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2351_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2374_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2349_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2349_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_val_2382_; lean_object* v___x_2383_; 
lean_dec(v_id_1835_);
v_val_2382_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2383_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2382_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v_pat_1841_ = v_a_2384_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_stx_1836_);
v_a_2385_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2383_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2383_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
else
{
v___y_2248_ = v_a_1837_;
v___y_2249_ = v_a_1838_;
goto v___jp_2247_;
}
}
}
else
{
lean_dec(v___x_2300_);
v___y_2248_ = v_a_1837_;
v___y_2249_ = v_a_1838_;
goto v___jp_2247_;
}
}
}
}
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2471_ = lean_unsigned_to_nat(1u);
v___x_2472_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2471_);
lean_inc(v___x_2472_);
v___x_2473_ = l_Lean_Syntax_matchesNull(v___x_2472_, v___x_2471_);
if (v___x_2473_ == 0)
{
lean_dec(v___x_2472_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_quotContext_x3f_2478_; lean_object* v___x_2479_; lean_object* v_a_2481_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v_quotContext_x3f_2478_ = lean_ctor_get(v_a_1837_, 5);
v___x_2479_ = l_Lean_SourceInfo_fromRef(v_a_2475_, v___x_2473_);
lean_dec(v_a_2475_);
if (lean_obj_tag(v_quotContext_x3f_2478_) == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v_a_2481_ = v_a_2513_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v___x_2479_);
lean_dec(v_a_2477_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2514_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2512_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2512_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v_val_2522_; 
v_val_2522_ = lean_ctor_get(v_quotContext_x3f_2478_, 0);
lean_inc(v_val_2522_);
v_a_2481_ = v_val_2522_;
goto v___jp_2480_;
}
v___jp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2482_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2484_ = l_Lean_addMacroScope(v_a_2481_, v___x_2483_, v_a_2477_);
v___x_2485_ = lean_box(0);
lean_inc_n(v___x_2479_, 3);
v___x_2486_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2479_);
lean_ctor_set(v___x_2486_, 1, v___x_2482_);
lean_ctor_set(v___x_2486_, 2, v___x_2484_);
lean_ctor_set(v___x_2486_, 3, v___x_2485_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2479_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2490_ = l_Lean_Syntax_node1(v___x_2479_, v___x_2489_, v_stx_1836_);
v___x_2491_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2503_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2503_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2503_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2479_);
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2479_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node4(v___x_2479_, v___x_1848_, v___x_2486_, v___x_2488_, v___x_2490_, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v_a_2492_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2499_);
v___x_2501_ = v___x_2494_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v___x_2490_);
lean_dec_ref_known(v___x_2488_, 2);
lean_dec_ref_known(v___x_2486_, 4);
lean_dec(v___x_2479_);
v_a_2504_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2491_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2491_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_a_2475_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2523_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2476_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2476_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2531_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2474_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2474_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_val_2539_; lean_object* v___x_2540_; 
lean_dec(v_id_1835_);
v_val_2539_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2540_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2539_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v_pat_1841_ = v_a_2541_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_stx_1836_);
v_a_2542_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2540_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2540_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v___x_2550_; lean_object* v_stx_2551_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2581_; lean_object* v___y_2582_; 
v___x_2550_ = lean_unsigned_to_nat(0u);
v_stx_2551_ = l_Lean_Syntax_getArg(v___x_2472_, v___x_2550_);
lean_dec(v___x_2472_);
v___x_2569_ = lean_unsigned_to_nat(2u);
v___x_2570_ = lean_unsigned_to_nat(3u);
v___x_2571_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2570_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2571_);
v___x_2727_ = l_Lean_Syntax_isOfKind(v___x_2571_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_dec(v___x_2571_);
lean_dec(v_stx_2551_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v_quotContext_x3f_2732_; lean_object* v___x_2733_; lean_object* v_a_2735_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v_quotContext_x3f_2732_ = lean_ctor_get(v_a_1837_, 5);
v___x_2733_ = l_Lean_SourceInfo_fromRef(v_a_2729_, v___x_2057_);
lean_dec(v_a_2729_);
if (lean_obj_tag(v_quotContext_x3f_2732_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v_a_2735_ = v_a_2767_;
goto v___jp_2734_;
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v___x_2733_);
lean_dec(v_a_2731_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2768_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2766_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2766_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_val_2776_; 
v_val_2776_ = lean_ctor_get(v_quotContext_x3f_2732_, 0);
lean_inc(v_val_2776_);
v_a_2735_ = v_val_2776_;
goto v___jp_2734_;
}
v___jp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2738_ = l_Lean_addMacroScope(v_a_2735_, v___x_2737_, v_a_2731_);
v___x_2739_ = lean_box(0);
lean_inc_n(v___x_2733_, 3);
v___x_2740_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2733_);
lean_ctor_set(v___x_2740_, 1, v___x_2736_);
lean_ctor_set(v___x_2740_, 2, v___x_2738_);
lean_ctor_set(v___x_2740_, 3, v___x_2739_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2733_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2744_ = l_Lean_Syntax_node1(v___x_2733_, v___x_2743_, v_stx_1836_);
v___x_2745_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2757_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2733_);
v___x_2751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2733_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l_Lean_Syntax_node4(v___x_2733_, v___x_1848_, v___x_2740_, v___x_2742_, v___x_2744_, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v_a_2746_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2753_);
v___x_2755_ = v___x_2748_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v___x_2744_);
lean_dec_ref_known(v___x_2742_, 2);
lean_dec_ref_known(v___x_2740_, 4);
lean_dec(v___x_2733_);
v_a_2758_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2745_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2745_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_a_2729_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2777_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2730_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2730_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2785_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2728_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2728_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_val_2793_; lean_object* v___x_2794_; 
lean_dec(v_id_1835_);
v_val_2793_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2793_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2794_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2793_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v_pat_1841_ = v_a_2795_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_stx_1836_);
v_a_2796_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2794_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2794_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
else
{
goto v___jp_2631_;
}
}
else
{
goto v___jp_2631_;
}
v___jp_2552_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2558_ = lean_string_append(v___y_2556_, v___x_2557_);
lean_inc(v___y_2554_);
v___x_2559_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2554_, v_stx_2551_, v_id_1835_, v___x_2558_, v___y_2555_, v___y_2553_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v_pat_1841_ = v_a_2560_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_stx_1836_);
v_a_2561_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2559_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2559_);
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
v___jp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2576_ = l_Lean_Syntax_isStrLit_x3f(v___x_2571_);
lean_dec(v___x_2571_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2578_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2577_);
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___x_2575_;
v___y_2555_ = v___y_2573_;
v___y_2556_ = v___x_2578_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2579_; 
v_val_2579_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v___x_2576_, 1);
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___x_2575_;
v___y_2555_ = v___y_2573_;
v___y_2556_ = v_val_2579_;
goto v___jp_2552_;
}
}
v___jp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(5u);
v___x_2584_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2583_);
v___x_2585_ = l_Lean_Syntax_isNone(v___x_2584_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; 
v___x_2586_ = l_Lean_Syntax_matchesNull(v___x_2584_, v___x_2569_);
if (v___x_2586_ == 0)
{
lean_dec(v___x_2571_);
lean_dec(v_stx_2551_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Elab_Command_getRef___redArg(v___y_2581_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2589_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2589_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2581_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v_quotContext_x3f_2591_; lean_object* v___x_2592_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v_quotContext_x3f_2591_ = lean_ctor_get(v___y_2581_, 5);
v___x_2592_ = l_Lean_SourceInfo_fromRef(v_a_2588_, v___x_2586_);
lean_dec(v_a_2588_);
if (lean_obj_tag(v_quotContext_x3f_2591_) == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2582_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___y_1954_ = v_a_2590_;
v___y_1955_ = v___y_2581_;
v___y_1956_ = v___x_2592_;
v___y_1957_ = v___y_2582_;
v_a_1958_ = v_a_2594_;
goto v___jp_1953_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v___x_2592_);
lean_dec(v_a_2590_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2595_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2593_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2593_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_val_2603_; 
v_val_2603_ = lean_ctor_get(v_quotContext_x3f_2591_, 0);
lean_inc(v_val_2603_);
v___y_1954_ = v_a_2590_;
v___y_1955_ = v___y_2581_;
v___y_1956_ = v___x_2592_;
v___y_1957_ = v___y_2582_;
v_a_1958_ = v_val_2603_;
goto v___jp_1953_;
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_a_2588_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2604_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2589_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2589_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2612_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2587_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2587_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_val_2620_; lean_object* v___x_2621_; 
lean_dec(v_id_1835_);
v_val_2620_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2620_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2621_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2620_, v___y_2581_, v___y_2582_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v_pat_1841_ = v_a_2622_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_stx_1836_);
v_a_2623_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2621_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1834_);
v___y_2573_ = v___y_2581_;
v___y_2574_ = v___y_2582_;
goto v___jp_2572_;
}
}
else
{
lean_dec(v___x_2584_);
lean_dec(v_id_x3f_1834_);
v___y_2573_ = v___y_2581_;
v___y_2574_ = v___y_2582_;
goto v___jp_2572_;
}
}
v___jp_2631_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = lean_unsigned_to_nat(4u);
v___x_2633_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2632_);
v___x_2634_ = l_Lean_Syntax_isNone(v___x_2633_);
if (v___x_2634_ == 0)
{
uint8_t v___x_2635_; 
lean_inc(v___x_2633_);
v___x_2635_ = l_Lean_Syntax_matchesNull(v___x_2633_, v___x_2569_);
if (v___x_2635_ == 0)
{
lean_dec(v___x_2633_);
lean_dec(v___x_2571_);
lean_dec(v_stx_2551_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v___x_2638_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v_quotContext_x3f_2640_; lean_object* v___x_2641_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v_quotContext_x3f_2640_ = lean_ctor_get(v_a_1837_, 5);
v___x_2641_ = l_Lean_SourceInfo_fromRef(v_a_2637_, v___x_2635_);
lean_dec(v_a_2637_);
if (lean_obj_tag(v_quotContext_x3f_2640_) == 0)
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___y_1990_ = v_a_2639_;
v___y_1991_ = v___x_2641_;
v_a_1992_ = v_a_2643_;
goto v___jp_1989_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___x_2641_);
lean_dec(v_a_2639_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2644_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2642_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2642_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v_val_2652_; 
v_val_2652_ = lean_ctor_get(v_quotContext_x3f_2640_, 0);
lean_inc(v_val_2652_);
v___y_1990_ = v_a_2639_;
v___y_1991_ = v___x_2641_;
v_a_1992_ = v_val_2652_;
goto v___jp_1989_;
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_a_2637_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2653_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2638_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2638_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2661_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2636_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2636_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
lean_dec(v_id_1835_);
v_val_2669_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2670_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2669_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v_pat_1841_ = v_a_2671_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_stx_1836_);
v_a_2672_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2670_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
else
{
lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___x_2680_ = l_Lean_Syntax_getArg(v___x_2633_, v___x_2471_);
lean_dec(v___x_2633_);
v___x_2681_ = l_Lean_Syntax_matchesNull(v___x_2680_, v___x_2471_);
if (v___x_2681_ == 0)
{
lean_dec(v___x_2571_);
lean_dec(v_stx_2551_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v_quotContext_x3f_2686_; lean_object* v___x_2687_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v_quotContext_x3f_2686_ = lean_ctor_get(v_a_1837_, 5);
v___x_2687_ = l_Lean_SourceInfo_fromRef(v_a_2683_, v___x_2681_);
lean_dec(v_a_2683_);
if (lean_obj_tag(v_quotContext_x3f_2686_) == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___y_2024_ = v___x_2687_;
v___y_2025_ = v_a_2685_;
v_a_2026_ = v_a_2689_;
goto v___jp_2023_;
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v___x_2687_);
lean_dec(v_a_2685_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2690_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2688_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_val_2698_; 
v_val_2698_ = lean_ctor_get(v_quotContext_x3f_2686_, 0);
lean_inc(v_val_2698_);
v___y_2024_ = v___x_2687_;
v___y_2025_ = v_a_2685_;
v_a_2026_ = v_val_2698_;
goto v___jp_2023_;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_a_2683_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2699_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2684_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2684_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2707_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2682_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2682_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
else
{
lean_object* v_val_2715_; lean_object* v___x_2716_; 
lean_dec(v_id_1835_);
v_val_2715_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2716_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2715_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v_pat_1841_ = v_a_2717_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_stx_1836_);
v_a_2718_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2716_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2716_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
else
{
v___y_2581_ = v_a_1837_;
v___y_2582_ = v_a_1838_;
goto v___jp_2580_;
}
}
}
else
{
lean_dec(v___x_2633_);
v___y_2581_ = v_a_1837_;
v___y_2582_ = v_a_1838_;
goto v___jp_2580_;
}
}
}
}
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2804_);
v___x_2806_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2807_ = l_Lean_Syntax_matchesIdent(v___x_2805_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2809_ = l_Lean_Syntax_matchesIdent(v___x_2805_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2811_ = l_Lean_Syntax_matchesIdent(v___x_2805_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2813_ = l_Lean_Syntax_matchesIdent(v___x_2805_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2815_ = l_Lean_Syntax_matchesIdent(v___x_2805_, v___x_2814_);
lean_dec(v___x_2805_);
if (v___x_2815_ == 0)
{
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v_quotContext_x3f_2820_; lean_object* v___x_2821_; lean_object* v_a_2823_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v_quotContext_x3f_2820_ = lean_ctor_get(v_a_1837_, 5);
v___x_2821_ = l_Lean_SourceInfo_fromRef(v_a_2817_, v___x_2815_);
lean_dec(v_a_2817_);
if (lean_obj_tag(v_quotContext_x3f_2820_) == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v_a_2823_ = v_a_2855_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v___x_2821_);
lean_dec(v_a_2819_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2856_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2854_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2854_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_val_2864_; 
v_val_2864_ = lean_ctor_get(v_quotContext_x3f_2820_, 0);
lean_inc(v_val_2864_);
v_a_2823_ = v_val_2864_;
goto v___jp_2822_;
}
v___jp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2824_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2825_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2826_ = l_Lean_addMacroScope(v_a_2823_, v___x_2825_, v_a_2819_);
v___x_2827_ = lean_box(0);
lean_inc_n(v___x_2821_, 3);
v___x_2828_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2821_);
lean_ctor_set(v___x_2828_, 1, v___x_2824_);
lean_ctor_set(v___x_2828_, 2, v___x_2826_);
lean_ctor_set(v___x_2828_, 3, v___x_2827_);
v___x_2829_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2821_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2832_ = l_Lean_Syntax_node1(v___x_2821_, v___x_2831_, v_stx_1836_);
v___x_2833_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2845_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2845_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2845_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2838_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2821_);
v___x_2839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2821_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = l_Lean_Syntax_node4(v___x_2821_, v___x_1848_, v___x_2828_, v___x_2830_, v___x_2832_, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v_a_2834_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2841_);
v___x_2843_ = v___x_2836_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v___x_2832_);
lean_dec_ref_known(v___x_2830_, 2);
lean_dec_ref_known(v___x_2828_, 4);
lean_dec(v___x_2821_);
v_a_2846_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2833_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2833_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2817_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2865_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2818_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2818_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2873_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2816_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2816_);
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
else
{
lean_object* v_val_2881_; lean_object* v___x_2882_; 
lean_dec(v_id_1835_);
v_val_2881_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2882_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2881_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v_pat_1841_ = v_a_2883_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_stx_1836_);
v_a_2884_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2882_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_unsigned_to_nat(2u);
v___x_2894_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_2893_);
lean_inc(v___x_2894_);
v___x_2895_ = l_Lean_Syntax_matchesNull(v___x_2894_, v___x_2892_);
if (v___x_2895_ == 0)
{
lean_dec(v___x_2894_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_quotContext_x3f_2900_; lean_object* v___x_2901_; lean_object* v_a_2903_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v_quotContext_x3f_2900_ = lean_ctor_get(v_a_1837_, 5);
v___x_2901_ = l_Lean_SourceInfo_fromRef(v_a_2897_, v___x_2895_);
lean_dec(v_a_2897_);
if (lean_obj_tag(v_quotContext_x3f_2900_) == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v_a_2903_ = v_a_2935_;
goto v___jp_2902_;
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v___x_2901_);
lean_dec(v_a_2899_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2936_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2934_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v_val_2944_; 
v_val_2944_ = lean_ctor_get(v_quotContext_x3f_2900_, 0);
lean_inc(v_val_2944_);
v_a_2903_ = v_val_2944_;
goto v___jp_2902_;
}
v___jp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2904_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2905_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2906_ = l_Lean_addMacroScope(v_a_2903_, v___x_2905_, v_a_2899_);
v___x_2907_ = lean_box(0);
lean_inc_n(v___x_2901_, 3);
v___x_2908_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2901_);
lean_ctor_set(v___x_2908_, 1, v___x_2904_);
lean_ctor_set(v___x_2908_, 2, v___x_2906_);
lean_ctor_set(v___x_2908_, 3, v___x_2907_);
v___x_2909_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2901_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2912_ = l_Lean_Syntax_node1(v___x_2901_, v___x_2911_, v_stx_1836_);
v___x_2913_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2925_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2925_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2925_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_2901_);
v___x_2919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2901_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = l_Lean_Syntax_node4(v___x_2901_, v___x_1848_, v___x_2908_, v___x_2910_, v___x_2912_, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v_a_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2921_);
v___x_2923_ = v___x_2916_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v___x_2912_);
lean_dec_ref_known(v___x_2910_, 2);
lean_dec_ref_known(v___x_2908_, 4);
lean_dec(v___x_2901_);
v_a_2926_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2913_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2913_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_a_2897_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2945_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2898_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2898_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_2953_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2896_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2896_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_object* v_val_2961_; lean_object* v___x_2962_; 
lean_dec(v_id_1835_);
v_val_2961_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_2961_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_2962_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_2961_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v_pat_1841_ = v_a_2963_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_stx_1836_);
v_a_2964_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2962_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2962_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
else
{
lean_object* v_stx_2972_; lean_object* v___x_2973_; 
lean_dec(v_stx_1836_);
v_stx_2972_ = l_Lean_Syntax_getArg(v___x_2894_, v___x_2804_);
lean_dec(v___x_2894_);
v___x_2973_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1834_, v_id_1835_, v_stx_2972_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v_fst_2975_; lean_object* v_snd_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3036_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v_fst_2975_ = lean_ctor_get(v_a_2974_, 0);
v_snd_2976_ = lean_ctor_get(v_a_2974_, 1);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_a_2974_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2978_ = v_a_2974_;
v_isShared_2979_ = v_isSharedCheck_3036_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_snd_2976_);
lean_inc(v_fst_2975_);
lean_dec(v_a_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3036_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3019_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3019_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3019_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v_quotContext_x3f_2987_; lean_object* v___x_2988_; lean_object* v_a_2990_; 
v_quotContext_x3f_2987_ = lean_ctor_get(v_a_1837_, 5);
v___x_2988_ = l_Lean_SourceInfo_fromRef(v_a_2981_, v___x_2813_);
lean_dec(v_a_2981_);
if (lean_obj_tag(v_quotContext_x3f_2987_) == 0)
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v_a_2990_ = v_a_3009_;
goto v___jp_2989_;
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v___x_2988_);
lean_del_object(v___x_2985_);
lean_dec(v_a_2983_);
lean_del_object(v___x_2978_);
lean_dec(v_snd_2976_);
lean_dec(v_fst_2975_);
v_a_3010_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3008_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3008_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v_val_3018_; 
v_val_3018_ = lean_ctor_get(v_quotContext_x3f_2987_, 0);
lean_inc(v_val_3018_);
v_a_2990_ = v_val_3018_;
goto v___jp_2989_;
}
v___jp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_2991_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_2992_ = l_Lean_addMacroScope(v_a_2990_, v___x_2814_, v_a_2983_);
v___x_2993_ = lean_box(0);
lean_inc_n(v___x_2988_, 4);
v___x_2994_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2988_);
lean_ctor_set(v___x_2994_, 1, v___x_2991_);
lean_ctor_set(v___x_2994_, 2, v___x_2992_);
lean_ctor_set(v___x_2994_, 3, v___x_2993_);
v___x_2995_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2988_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_2998_ = l_Lean_Syntax_node1(v___x_2988_, v___x_2997_, v_fst_2975_);
v___x_2999_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2988_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Lean_Syntax_node4(v___x_2988_, v___x_1848_, v___x_2994_, v___x_2996_, v___x_2998_, v___x_3000_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_3001_);
v___x_3003_ = v___x_2978_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_snd_2976_);
v___x_3003_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_3003_);
v___x_3005_ = v___x_2985_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_a_2981_);
lean_del_object(v___x_2978_);
lean_dec(v_snd_2976_);
lean_dec(v_fst_2975_);
v_a_3020_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_2982_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_2982_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_del_object(v___x_2978_);
lean_dec(v_snd_2976_);
lean_dec(v_fst_2975_);
v_a_3028_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2980_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2980_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
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
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
else
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
lean_dec(v___x_2805_);
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_unsigned_to_nat(2u);
v___x_3039_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_3038_);
lean_inc(v___x_3039_);
v___x_3040_ = l_Lean_Syntax_matchesNull(v___x_3039_, v___x_3037_);
if (v___x_3040_ == 0)
{
lean_dec(v___x_3039_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_quotContext_x3f_3045_; lean_object* v___x_3046_; lean_object* v_a_3048_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v_quotContext_x3f_3045_ = lean_ctor_get(v_a_1837_, 5);
v___x_3046_ = l_Lean_SourceInfo_fromRef(v_a_3042_, v___x_3040_);
lean_dec(v_a_3042_);
if (lean_obj_tag(v_quotContext_x3f_3045_) == 0)
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v_a_3048_ = v_a_3080_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v___x_3046_);
lean_dec(v_a_3044_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3081_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3079_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3079_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v_val_3089_; 
v_val_3089_ = lean_ctor_get(v_quotContext_x3f_3045_, 0);
lean_inc(v_val_3089_);
v_a_3048_ = v_val_3089_;
goto v___jp_3047_;
}
v___jp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3049_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3050_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3051_ = l_Lean_addMacroScope(v_a_3048_, v___x_3050_, v_a_3044_);
v___x_3052_ = lean_box(0);
lean_inc_n(v___x_3046_, 3);
v___x_3053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3046_);
lean_ctor_set(v___x_3053_, 1, v___x_3049_);
lean_ctor_set(v___x_3053_, 2, v___x_3051_);
lean_ctor_set(v___x_3053_, 3, v___x_3052_);
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3046_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3057_ = l_Lean_Syntax_node1(v___x_3046_, v___x_3056_, v_stx_1836_);
v___x_3058_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3070_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3070_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3070_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3063_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3046_);
v___x_3064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3046_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = l_Lean_Syntax_node4(v___x_3046_, v___x_1848_, v___x_3053_, v___x_3055_, v___x_3057_, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v_a_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3066_);
v___x_3068_ = v___x_3061_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v___x_3057_);
lean_dec_ref_known(v___x_3055_, 2);
lean_dec_ref_known(v___x_3053_, 4);
lean_dec(v___x_3046_);
v_a_3071_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3058_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3058_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_a_3042_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3090_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3043_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3043_);
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
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3098_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3041_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3041_);
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
else
{
lean_object* v_val_3106_; lean_object* v___x_3107_; 
lean_dec(v_id_1835_);
v_val_3106_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3106_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3107_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3106_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v_pat_1841_ = v_a_3108_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v_stx_1836_);
v_a_3109_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3107_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3107_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = l_Lean_Syntax_getArg(v___x_3039_, v___x_2804_);
lean_dec(v___x_3039_);
v___x_3118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3117_);
v___x_3119_ = l_Lean_Syntax_isOfKind(v___x_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_dec(v___x_3117_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_quotContext_x3f_3124_; lean_object* v___x_3125_; lean_object* v_a_3127_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v_quotContext_x3f_3124_ = lean_ctor_get(v_a_1837_, 5);
v___x_3125_ = l_Lean_SourceInfo_fromRef(v_a_3121_, v___x_3119_);
lean_dec(v_a_3121_);
if (lean_obj_tag(v_quotContext_x3f_3124_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v_a_3127_ = v_a_3159_;
goto v___jp_3126_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v___x_3125_);
lean_dec(v_a_3123_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3160_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3158_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3158_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_val_3168_; 
v_val_3168_ = lean_ctor_get(v_quotContext_x3f_3124_, 0);
lean_inc(v_val_3168_);
v_a_3127_ = v_val_3168_;
goto v___jp_3126_;
}
v___jp_3126_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3128_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3129_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3130_ = l_Lean_addMacroScope(v_a_3127_, v___x_3129_, v_a_3123_);
v___x_3131_ = lean_box(0);
lean_inc_n(v___x_3125_, 3);
v___x_3132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3125_);
lean_ctor_set(v___x_3132_, 1, v___x_3128_);
lean_ctor_set(v___x_3132_, 2, v___x_3130_);
lean_ctor_set(v___x_3132_, 3, v___x_3131_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3125_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3136_ = l_Lean_Syntax_node1(v___x_3125_, v___x_3135_, v_stx_1836_);
v___x_3137_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3149_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3142_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3125_);
v___x_3143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3125_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = l_Lean_Syntax_node4(v___x_3125_, v___x_1848_, v___x_3132_, v___x_3134_, v___x_3136_, v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v_a_3138_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3145_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v___x_3136_);
lean_dec_ref_known(v___x_3134_, 2);
lean_dec_ref_known(v___x_3132_, 4);
lean_dec(v___x_3125_);
v_a_3150_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3137_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3137_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_a_3121_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3169_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3122_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3122_);
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
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3177_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3120_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3120_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_val_3185_; lean_object* v___x_3186_; 
lean_dec(v_id_1835_);
v_val_3185_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3185_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3186_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3185_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v_pat_1841_ = v_a_3187_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v_stx_1836_);
v_a_3188_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3186_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3186_);
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
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3196_ = l_Lean_Syntax_getArg(v___x_3117_, v___x_2804_);
v___x_3197_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3198_ = l_Lean_Syntax_matchesIdent(v___x_3196_, v___x_3197_);
lean_dec(v___x_3196_);
if (v___x_3198_ == 0)
{
lean_dec(v___x_3117_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v_quotContext_x3f_3203_; lean_object* v___x_3204_; lean_object* v_a_3206_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v_quotContext_x3f_3203_ = lean_ctor_get(v_a_1837_, 5);
v___x_3204_ = l_Lean_SourceInfo_fromRef(v_a_3200_, v___x_3198_);
lean_dec(v_a_3200_);
if (lean_obj_tag(v_quotContext_x3f_3203_) == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v_a_3206_ = v_a_3238_;
goto v___jp_3205_;
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v___x_3204_);
lean_dec(v_a_3202_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3239_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3237_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3237_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_val_3247_; 
v_val_3247_ = lean_ctor_get(v_quotContext_x3f_3203_, 0);
lean_inc(v_val_3247_);
v_a_3206_ = v_val_3247_;
goto v___jp_3205_;
}
v___jp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3207_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3208_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3209_ = l_Lean_addMacroScope(v_a_3206_, v___x_3208_, v_a_3202_);
v___x_3210_ = lean_box(0);
lean_inc_n(v___x_3204_, 3);
v___x_3211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3204_);
lean_ctor_set(v___x_3211_, 1, v___x_3207_);
lean_ctor_set(v___x_3211_, 2, v___x_3209_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
v___x_3212_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3204_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3215_ = l_Lean_Syntax_node1(v___x_3204_, v___x_3214_, v_stx_1836_);
v___x_3216_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3228_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3228_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3228_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3221_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3204_);
v___x_3222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3204_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_Syntax_node4(v___x_3204_, v___x_1848_, v___x_3211_, v___x_3213_, v___x_3215_, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v_a_3217_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3224_);
v___x_3226_ = v___x_3219_;
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
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v___x_3215_);
lean_dec_ref_known(v___x_3213_, 2);
lean_dec_ref_known(v___x_3211_, 4);
lean_dec(v___x_3204_);
v_a_3229_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3216_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3216_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_a_3200_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3248_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3201_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3201_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3256_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3199_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3199_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_val_3264_; lean_object* v___x_3265_; 
lean_dec(v_id_1835_);
v_val_3264_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3265_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3264_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v_pat_1841_ = v_a_3266_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_stx_1836_);
v_a_3267_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3265_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3265_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
else
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = l_Lean_Syntax_getArg(v___x_3117_, v___x_3037_);
lean_dec(v___x_3117_);
v___x_3276_ = l_Lean_Syntax_matchesNull(v___x_3275_, v___x_2804_);
if (v___x_3276_ == 0)
{
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v_quotContext_x3f_3281_; lean_object* v___x_3282_; lean_object* v_a_3284_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v_quotContext_x3f_3281_ = lean_ctor_get(v_a_1837_, 5);
v___x_3282_ = l_Lean_SourceInfo_fromRef(v_a_3278_, v___x_3276_);
lean_dec(v_a_3278_);
if (lean_obj_tag(v_quotContext_x3f_3281_) == 0)
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v_a_3284_ = v_a_3316_;
goto v___jp_3283_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v___x_3282_);
lean_dec(v_a_3280_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3317_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3315_);
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
lean_object* v_val_3325_; 
v_val_3325_ = lean_ctor_get(v_quotContext_x3f_3281_, 0);
lean_inc(v_val_3325_);
v_a_3284_ = v_val_3325_;
goto v___jp_3283_;
}
v___jp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3285_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3287_ = l_Lean_addMacroScope(v_a_3284_, v___x_3286_, v_a_3280_);
v___x_3288_ = lean_box(0);
lean_inc_n(v___x_3282_, 3);
v___x_3289_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3282_);
lean_ctor_set(v___x_3289_, 1, v___x_3285_);
lean_ctor_set(v___x_3289_, 2, v___x_3287_);
lean_ctor_set(v___x_3289_, 3, v___x_3288_);
v___x_3290_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3282_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3293_ = l_Lean_Syntax_node1(v___x_3282_, v___x_3292_, v_stx_1836_);
v___x_3294_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3306_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3306_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3306_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3282_);
v___x_3300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3282_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_Syntax_node4(v___x_3282_, v___x_1848_, v___x_3289_, v___x_3291_, v___x_3293_, v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v_a_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3302_);
v___x_3304_ = v___x_3297_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v___x_3293_);
lean_dec_ref_known(v___x_3291_, 2);
lean_dec_ref_known(v___x_3289_, 4);
lean_dec(v___x_3282_);
v_a_3307_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3294_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3294_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_a_3278_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3326_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3279_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3279_);
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
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3334_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3277_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3277_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v_val_3342_; lean_object* v___x_3343_; 
lean_dec(v_id_1835_);
v_val_3342_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3343_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3342_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v_pat_1841_ = v_a_3344_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_stx_1836_);
v_a_3345_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3343_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3343_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec(v_id_x3f_1834_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3354_ = lean_box(0);
v___x_3355_ = l_Lean_Syntax_mkAntiquotNode(v___x_3353_, v_id_1835_, v___x_2804_, v___x_3354_, v___x_2811_);
v_pat_1841_ = v___x_3355_;
goto v___jp_1840_;
}
}
}
}
}
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
lean_dec(v___x_2805_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_unsigned_to_nat(2u);
v___x_3358_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_3357_);
lean_inc(v___x_3358_);
v___x_3359_ = l_Lean_Syntax_matchesNull(v___x_3358_, v___x_3356_);
if (v___x_3359_ == 0)
{
lean_dec(v___x_3358_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v_quotContext_x3f_3364_; lean_object* v___x_3365_; lean_object* v_a_3367_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v_quotContext_x3f_3364_ = lean_ctor_get(v_a_1837_, 5);
v___x_3365_ = l_Lean_SourceInfo_fromRef(v_a_3361_, v___x_3359_);
lean_dec(v_a_3361_);
if (lean_obj_tag(v_quotContext_x3f_3364_) == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v_a_3367_ = v_a_3399_;
goto v___jp_3366_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v___x_3365_);
lean_dec(v_a_3363_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3400_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3398_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_val_3408_; 
v_val_3408_ = lean_ctor_get(v_quotContext_x3f_3364_, 0);
lean_inc(v_val_3408_);
v_a_3367_ = v_val_3408_;
goto v___jp_3366_;
}
v___jp_3366_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3368_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3370_ = l_Lean_addMacroScope(v_a_3367_, v___x_3369_, v_a_3363_);
v___x_3371_ = lean_box(0);
lean_inc_n(v___x_3365_, 3);
v___x_3372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3365_);
lean_ctor_set(v___x_3372_, 1, v___x_3368_);
lean_ctor_set(v___x_3372_, 2, v___x_3370_);
lean_ctor_set(v___x_3372_, 3, v___x_3371_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3365_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3376_ = l_Lean_Syntax_node1(v___x_3365_, v___x_3375_, v_stx_1836_);
v___x_3377_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3389_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3389_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3389_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3365_);
v___x_3383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3365_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = l_Lean_Syntax_node4(v___x_3365_, v___x_1848_, v___x_3372_, v___x_3374_, v___x_3376_, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v_a_3378_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3385_);
v___x_3387_ = v___x_3380_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v___x_3376_);
lean_dec_ref_known(v___x_3374_, 2);
lean_dec_ref_known(v___x_3372_, 4);
lean_dec(v___x_3365_);
v_a_3390_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3377_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3377_);
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
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_a_3361_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3409_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3362_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3362_);
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
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3417_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3360_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3360_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v_val_3425_; lean_object* v___x_3426_; 
lean_dec(v_id_1835_);
v_val_3425_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3426_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3425_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v_pat_1841_ = v_a_3427_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_stx_1836_);
v_a_3428_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3426_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3426_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v_stx_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_id_x3f_1834_);
v_stx_3436_ = l_Lean_Syntax_getArg(v___x_3358_, v___x_2804_);
lean_dec(v___x_3358_);
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3438_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2808_, v_stx_3436_, v_id_1835_, v___x_3437_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v_pat_1841_ = v_a_3439_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_stx_1836_);
v_a_3440_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3438_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3438_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
lean_dec(v___x_2805_);
v___x_3448_ = lean_unsigned_to_nat(1u);
v___x_3449_ = lean_unsigned_to_nat(2u);
v___x_3450_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_3449_);
lean_inc(v___x_3450_);
v___x_3451_ = l_Lean_Syntax_matchesNull(v___x_3450_, v___x_3448_);
if (v___x_3451_ == 0)
{
lean_dec(v___x_3450_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v_quotContext_x3f_3456_; lean_object* v___x_3457_; lean_object* v_a_3459_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v_quotContext_x3f_3456_ = lean_ctor_get(v_a_1837_, 5);
v___x_3457_ = l_Lean_SourceInfo_fromRef(v_a_3453_, v___x_3451_);
lean_dec(v_a_3453_);
if (lean_obj_tag(v_quotContext_x3f_3456_) == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v_a_3459_ = v_a_3491_;
goto v___jp_3458_;
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3492_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3490_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v_val_3500_; 
v_val_3500_ = lean_ctor_get(v_quotContext_x3f_3456_, 0);
lean_inc(v_val_3500_);
v_a_3459_ = v_val_3500_;
goto v___jp_3458_;
}
v___jp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3460_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3461_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3462_ = l_Lean_addMacroScope(v_a_3459_, v___x_3461_, v_a_3455_);
v___x_3463_ = lean_box(0);
lean_inc_n(v___x_3457_, 3);
v___x_3464_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3457_);
lean_ctor_set(v___x_3464_, 1, v___x_3460_);
lean_ctor_set(v___x_3464_, 2, v___x_3462_);
lean_ctor_set(v___x_3464_, 3, v___x_3463_);
v___x_3465_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3457_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3468_ = l_Lean_Syntax_node1(v___x_3457_, v___x_3467_, v_stx_1836_);
v___x_3469_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3481_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3481_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3481_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3474_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3457_);
v___x_3475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3457_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = l_Lean_Syntax_node4(v___x_3457_, v___x_1848_, v___x_3464_, v___x_3466_, v___x_3468_, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v_a_3470_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3477_);
v___x_3479_ = v___x_3472_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec(v___x_3468_);
lean_dec_ref_known(v___x_3466_, 2);
lean_dec_ref_known(v___x_3464_, 4);
lean_dec(v___x_3457_);
v_a_3482_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3469_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3469_);
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
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec(v_a_3453_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3501_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3454_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3454_);
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
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3509_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3452_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3452_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v_val_3517_; lean_object* v___x_3518_; 
lean_dec(v_id_1835_);
v_val_3517_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3517_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3518_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3517_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v_pat_1841_ = v_a_3519_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v_stx_1836_);
v_a_3520_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3518_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3518_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
else
{
lean_object* v_stx_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v_id_x3f_1834_);
v_stx_3528_ = l_Lean_Syntax_getArg(v___x_3450_, v___x_2804_);
lean_dec(v___x_3450_);
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3530_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2808_, v_stx_3528_, v_id_1835_, v___x_3529_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v_pat_1841_ = v_a_3531_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v_stx_1836_);
v_a_3532_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3530_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3530_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
lean_dec(v___x_2805_);
v___x_3540_ = lean_unsigned_to_nat(1u);
v___x_3541_ = lean_unsigned_to_nat(2u);
v___x_3542_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_3541_);
lean_inc(v___x_3542_);
v___x_3543_ = l_Lean_Syntax_matchesNull(v___x_3542_, v___x_3540_);
if (v___x_3543_ == 0)
{
lean_dec(v___x_3542_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v_quotContext_x3f_3548_; lean_object* v___x_3549_; lean_object* v_a_3551_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v_quotContext_x3f_3548_ = lean_ctor_get(v_a_1837_, 5);
v___x_3549_ = l_Lean_SourceInfo_fromRef(v_a_3545_, v___x_3543_);
lean_dec(v_a_3545_);
if (lean_obj_tag(v_quotContext_x3f_3548_) == 0)
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v_a_3551_ = v_a_3583_;
goto v___jp_3550_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v___x_3549_);
lean_dec(v_a_3547_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3584_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3582_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3582_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_val_3592_; 
v_val_3592_ = lean_ctor_get(v_quotContext_x3f_3548_, 0);
lean_inc(v_val_3592_);
v_a_3551_ = v_val_3592_;
goto v___jp_3550_;
}
v___jp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3552_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3554_ = l_Lean_addMacroScope(v_a_3551_, v___x_3553_, v_a_3547_);
v___x_3555_ = lean_box(0);
lean_inc_n(v___x_3549_, 3);
v___x_3556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3549_);
lean_ctor_set(v___x_3556_, 1, v___x_3552_);
lean_ctor_set(v___x_3556_, 2, v___x_3554_);
lean_ctor_set(v___x_3556_, 3, v___x_3555_);
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3549_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3560_ = l_Lean_Syntax_node1(v___x_3549_, v___x_3559_, v_stx_1836_);
v___x_3561_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3573_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3573_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3573_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3549_);
v___x_3567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3549_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = l_Lean_Syntax_node4(v___x_3549_, v___x_1848_, v___x_3556_, v___x_3558_, v___x_3560_, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set(v___x_3569_, 1, v_a_3562_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3569_);
v___x_3571_ = v___x_3564_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v___x_3560_);
lean_dec_ref_known(v___x_3558_, 2);
lean_dec_ref_known(v___x_3556_, 4);
lean_dec(v___x_3549_);
v_a_3574_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3561_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3561_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec(v_a_3545_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3593_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3546_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3546_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3601_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3544_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3544_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v_val_3609_; lean_object* v___x_3610_; 
lean_dec(v_id_1835_);
v_val_3609_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3610_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3609_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v_pat_1841_ = v_a_3611_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_stx_1836_);
v_a_3612_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3610_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3610_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
else
{
lean_object* v_stx_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_dec(v_id_x3f_1834_);
v_stx_3620_ = l_Lean_Syntax_getArg(v___x_3542_, v___x_2804_);
lean_dec(v___x_3542_);
v___x_3621_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3622_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2806_, v_stx_3620_, v_id_1835_, v___x_3621_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v_pat_1841_ = v_a_3623_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_stx_1836_);
v_a_3624_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3622_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3622_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
}
v___jp_1849_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1855_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1857_ = l_Lean_addMacroScope(v_a_1854_, v___x_1856_, v___y_1850_);
v___x_1858_ = lean_box(0);
lean_inc_n(v___y_1853_, 3);
v___x_1859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1859_, 0, v___y_1853_);
lean_ctor_set(v___x_1859_, 1, v___x_1855_);
lean_ctor_set(v___x_1859_, 2, v___x_1857_);
lean_ctor_set(v___x_1859_, 3, v___x_1858_);
v___x_1860_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___y_1853_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_1863_ = l_Lean_Syntax_node1(v___y_1853_, v___x_1862_, v_stx_1836_);
v___x_1864_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1876_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1876_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1876_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1853_);
v___x_1870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___y_1853_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_Syntax_node4(v___y_1853_, v___x_1848_, v___x_1859_, v___x_1861_, v___x_1863_, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1872_);
v___x_1874_ = v___x_1867_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v___x_1863_);
lean_dec_ref_known(v___x_1861_, 2);
lean_dec_ref_known(v___x_1859_, 4);
lean_dec(v___y_1853_);
v_a_1877_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1864_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1864_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
v___jp_1885_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1889_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1890_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1891_ = l_Lean_addMacroScope(v_a_1888_, v___x_1890_, v___y_1886_);
v___x_1892_ = lean_box(0);
lean_inc_n(v___y_1887_, 3);
v___x_1893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1893_, 0, v___y_1887_);
lean_ctor_set(v___x_1893_, 1, v___x_1889_);
lean_ctor_set(v___x_1893_, 2, v___x_1891_);
lean_ctor_set(v___x_1893_, 3, v___x_1892_);
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___y_1887_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_1897_ = l_Lean_Syntax_node1(v___y_1887_, v___x_1896_, v_stx_1836_);
v___x_1898_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1910_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1910_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1910_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1887_);
v___x_1904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___y_1887_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_Syntax_node4(v___y_1887_, v___x_1848_, v___x_1893_, v___x_1895_, v___x_1897_, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1906_);
v___x_1908_ = v___x_1901_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v___x_1897_);
lean_dec_ref_known(v___x_1895_, 2);
lean_dec_ref_known(v___x_1893_, 4);
lean_dec(v___y_1887_);
v_a_1911_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1898_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1898_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
v___jp_1919_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1925_ = l_Lean_addMacroScope(v_a_1922_, v___x_1924_, v___y_1921_);
v___x_1926_ = lean_box(0);
lean_inc_n(v___y_1920_, 3);
v___x_1927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1927_, 0, v___y_1920_);
lean_ctor_set(v___x_1927_, 1, v___x_1923_);
lean_ctor_set(v___x_1927_, 2, v___x_1925_);
lean_ctor_set(v___x_1927_, 3, v___x_1926_);
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___y_1920_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_1931_ = l_Lean_Syntax_node1(v___y_1920_, v___x_1930_, v_stx_1836_);
v___x_1932_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
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
lean_inc(v___y_1920_);
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___y_1920_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_Syntax_node4(v___y_1920_, v___x_1848_, v___x_1927_, v___x_1929_, v___x_1931_, v___x_1938_);
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
lean_dec_ref_known(v___x_1929_, 2);
lean_dec_ref_known(v___x_1927_, 4);
lean_dec(v___y_1920_);
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
v___jp_1953_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1959_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1960_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1961_ = l_Lean_addMacroScope(v_a_1958_, v___x_1960_, v___y_1954_);
v___x_1962_ = lean_box(0);
lean_inc_n(v___y_1956_, 3);
v___x_1963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1963_, 0, v___y_1956_);
lean_ctor_set(v___x_1963_, 1, v___x_1959_);
lean_ctor_set(v___x_1963_, 2, v___x_1961_);
lean_ctor_set(v___x_1963_, 3, v___x_1962_);
v___x_1964_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___y_1956_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_1967_ = l_Lean_Syntax_node1(v___y_1956_, v___x_1966_, v_stx_1836_);
v___x_1968_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v___y_1955_, v___y_1957_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1980_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1973_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1956_);
v___x_1974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___y_1956_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_Syntax_node4(v___y_1956_, v___x_1848_, v___x_1963_, v___x_1965_, v___x_1967_, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_a_1969_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1976_);
v___x_1978_ = v___x_1971_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v___x_1967_);
lean_dec_ref_known(v___x_1965_, 2);
lean_dec_ref_known(v___x_1963_, 4);
lean_dec(v___y_1956_);
v_a_1981_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1968_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1968_);
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
v___jp_1989_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1993_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1994_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1995_ = l_Lean_addMacroScope(v_a_1992_, v___x_1994_, v___y_1990_);
v___x_1996_ = lean_box(0);
lean_inc_n(v___y_1991_, 3);
v___x_1997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1997_, 0, v___y_1991_);
lean_ctor_set(v___x_1997_, 1, v___x_1993_);
lean_ctor_set(v___x_1997_, 2, v___x_1995_);
lean_ctor_set(v___x_1997_, 3, v___x_1996_);
v___x_1998_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___y_1991_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2001_ = l_Lean_Syntax_node1(v___y_1991_, v___x_2000_, v_stx_1836_);
v___x_2002_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2014_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2014_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2014_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_1991_);
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___y_1991_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Lean_Syntax_node4(v___y_1991_, v___x_1848_, v___x_1997_, v___x_1999_, v___x_2001_, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v_a_2003_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2010_);
v___x_2012_ = v___x_2005_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v___x_2001_);
lean_dec_ref_known(v___x_1999_, 2);
lean_dec_ref_known(v___x_1997_, 4);
lean_dec(v___y_1991_);
v_a_2015_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2002_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2002_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
v___jp_2023_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2027_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2028_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2029_ = l_Lean_addMacroScope(v_a_2026_, v___x_2028_, v___y_2025_);
v___x_2030_ = lean_box(0);
lean_inc_n(v___y_2024_, 3);
v___x_2031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2031_, 0, v___y_2024_);
lean_ctor_set(v___x_2031_, 1, v___x_2027_);
lean_ctor_set(v___x_2031_, 2, v___x_2029_);
lean_ctor_set(v___x_2031_, 3, v___x_2030_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___y_2024_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_2035_ = l_Lean_Syntax_node1(v___y_2024_, v___x_2034_, v_stx_1836_);
v___x_2036_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2048_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2048_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2048_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___y_2024_);
v___x_2042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___y_2024_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_Syntax_node4(v___y_2024_, v___x_1848_, v___x_2031_, v___x_2033_, v___x_2035_, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v_a_2037_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2044_);
v___x_2046_ = v___x_2039_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_2035_);
lean_dec_ref_known(v___x_2033_, 2);
lean_dec_ref_known(v___x_2031_, 4);
lean_dec(v___y_2024_);
v_a_2049_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2036_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2036_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_3632_);
if (v___x_1845_ == 0)
{
lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3633_);
v___x_3658_ = l_Lean_Syntax_isOfKind(v___x_3633_, v___x_3657_);
if (v___x_3658_ == 0)
{
lean_dec(v___x_3633_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v_quotContext_x3f_3663_; lean_object* v___x_3664_; lean_object* v_a_3666_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v_quotContext_x3f_3663_ = lean_ctor_get(v_a_1837_, 5);
v___x_3664_ = l_Lean_SourceInfo_fromRef(v_a_3660_, v___x_1845_);
lean_dec(v_a_3660_);
if (lean_obj_tag(v_quotContext_x3f_3663_) == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v_a_3666_ = v_a_3699_;
goto v___jp_3665_;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v___x_3664_);
lean_dec(v_a_3662_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3700_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3698_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3698_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_val_3708_; 
v_val_3708_ = lean_ctor_get(v_quotContext_x3f_3663_, 0);
lean_inc(v_val_3708_);
v_a_3666_ = v_val_3708_;
goto v___jp_3665_;
}
v___jp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3667_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3668_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3669_ = l_Lean_addMacroScope(v_a_3666_, v___x_3668_, v_a_3662_);
v___x_3670_ = lean_box(0);
lean_inc_n(v___x_3664_, 3);
v___x_3671_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3664_);
lean_ctor_set(v___x_3671_, 1, v___x_3667_);
lean_ctor_set(v___x_3671_, 2, v___x_3669_);
lean_ctor_set(v___x_3671_, 3, v___x_3670_);
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3664_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3675_ = l_Lean_Syntax_node1(v___x_3664_, v___x_3674_, v_stx_1836_);
v___x_3676_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3689_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3689_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3689_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3681_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3664_);
v___x_3682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3664_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3684_ = l_Lean_Syntax_node4(v___x_3664_, v___x_3683_, v___x_3671_, v___x_3673_, v___x_3675_, v___x_3682_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_a_3677_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3685_);
v___x_3687_ = v___x_3679_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v___x_3675_);
lean_dec_ref_known(v___x_3673_, 2);
lean_dec_ref_known(v___x_3671_, 4);
lean_dec(v___x_3664_);
v_a_3690_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3676_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3676_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v_a_3660_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3709_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3661_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3661_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3717_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3659_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3659_);
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
else
{
lean_object* v_val_3725_; lean_object* v___x_3726_; 
lean_dec(v_id_1835_);
v_val_3725_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3725_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3726_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3725_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v_pat_1841_ = v_a_3727_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_stx_1836_);
v_a_3728_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3726_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3726_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1834_);
goto v___jp_3634_;
}
}
else
{
lean_dec(v_id_x3f_1834_);
goto v___jp_3634_;
}
v___jp_3634_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3635_, 0, v___x_3633_);
v___x_3636_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3635_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3639_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3640_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3641_ = lean_unsigned_to_nat(4u);
v___x_3642_ = lean_mk_empty_array_with_capacity(v___x_3641_);
v___x_3643_ = lean_array_push(v___x_3642_, v_a_3637_);
v___x_3644_ = lean_array_push(v___x_3643_, v___x_3639_);
v___x_3645_ = lean_array_push(v___x_3644_, v___x_3640_);
v___x_3646_ = lean_array_push(v___x_3645_, v_id_1835_);
v___x_3647_ = lean_box(2);
v___x_3648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v___x_3638_);
lean_ctor_set(v___x_3648_, 2, v___x_3646_);
v_pat_1841_ = v___x_3648_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3649_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3636_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3636_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
}
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3736_ = lean_unsigned_to_nat(0u);
v___x_3737_ = l_Lean_Syntax_getArg(v_stx_1836_, v___x_3736_);
v___x_3738_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3737_);
v___x_3739_ = l_Lean_Syntax_isOfKind(v___x_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_dec(v___x_3737_);
if (lean_obj_tag(v_id_x3f_1834_) == 0)
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Elab_Command_getRef___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1837_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v_quotContext_x3f_3744_; lean_object* v___x_3745_; lean_object* v_a_3747_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v_quotContext_x3f_3744_ = lean_ctor_get(v_a_1837_, 5);
v___x_3745_ = l_Lean_SourceInfo_fromRef(v_a_3741_, v___x_3739_);
lean_dec(v_a_3741_);
if (lean_obj_tag(v_quotContext_x3f_3744_) == 0)
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1838_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v_a_3747_ = v_a_3780_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v___x_3745_);
lean_dec(v_a_3743_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3781_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3779_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_val_3789_; 
v_val_3789_ = lean_ctor_get(v_quotContext_x3f_3744_, 0);
lean_inc(v_val_3789_);
v_a_3747_ = v_val_3789_;
goto v___jp_3746_;
}
v___jp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3748_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3749_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3750_ = l_Lean_addMacroScope(v_a_3747_, v___x_3749_, v_a_3743_);
v___x_3751_ = lean_box(0);
lean_inc_n(v___x_3745_, 3);
v___x_3752_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3745_);
lean_ctor_set(v___x_3752_, 1, v___x_3748_);
lean_ctor_set(v___x_3752_, 2, v___x_3750_);
lean_ctor_set(v___x_3752_, 3, v___x_3751_);
v___x_3753_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3745_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1836_);
v___x_3756_ = l_Lean_Syntax_node1(v___x_3745_, v___x_3755_, v_stx_1836_);
v___x_3757_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_id_1835_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3770_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3770_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3770_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
lean_inc(v___x_3745_);
v___x_3763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3745_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3765_ = l_Lean_Syntax_node4(v___x_3745_, v___x_3764_, v___x_3752_, v___x_3754_, v___x_3756_, v___x_3763_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v_a_3758_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___x_3766_);
v___x_3768_ = v___x_3760_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v___x_3756_);
lean_dec_ref_known(v___x_3754_, 2);
lean_dec_ref_known(v___x_3752_, 4);
lean_dec(v___x_3745_);
v_a_3771_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3757_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3757_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec(v_a_3741_);
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3790_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3742_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3742_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3798_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3740_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3740_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v_val_3806_; lean_object* v___x_3807_; 
lean_dec(v_id_1835_);
v_val_3806_ = lean_ctor_get(v_id_x3f_1834_, 0);
lean_inc(v_val_3806_);
lean_dec_ref_known(v_id_x3f_1834_, 1);
lean_inc(v_stx_1836_);
v___x_3807_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1836_, v_val_3806_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v_pat_1841_ = v_a_3808_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_stx_1836_);
v_a_3809_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3807_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3807_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec(v_id_x3f_1834_);
v___x_3817_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3817_, 0, v___x_3737_);
v___x_3818_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3817_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3818_, 1);
v___x_3820_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3821_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3822_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3823_ = lean_unsigned_to_nat(4u);
v___x_3824_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___x_3825_ = lean_array_push(v___x_3824_, v_a_3819_);
v___x_3826_ = lean_array_push(v___x_3825_, v___x_3821_);
v___x_3827_ = lean_array_push(v___x_3826_, v___x_3822_);
v___x_3828_ = lean_array_push(v___x_3827_, v_id_1835_);
v___x_3829_ = lean_box(2);
v___x_3830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set(v___x_3830_, 1, v___x_3820_);
lean_ctor_set(v___x_3830_, 2, v___x_3828_);
v_pat_1841_ = v___x_3830_;
goto v___jp_1840_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec(v_stx_1836_);
lean_dec(v_id_1835_);
v_a_3831_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3818_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3818_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
v___jp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_stx_1836_);
lean_ctor_set(v___x_1842_, 1, v_pat_1841_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3839_, lean_object* v_id_3840_, lean_object* v_stx_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3839_, v_id_3840_, v_stx_3841_, v_a_3842_, v_a_3843_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3846_, lean_object* v_x_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3847_, v___y_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3851_, lean_object* v_x_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3851_, v_x_3852_, v___y_3853_, v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec_ref(v_x_3852_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3856_, lean_object* v_ref_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3857_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3862_, lean_object* v_ref_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3862_, v_ref_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3878_, lean_object* v_x_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3879_, v___y_3880_, v___y_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3884_, lean_object* v_x_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3884_, v_x_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3890_, lean_object* v_as_x27_3891_, lean_object* v_b_3892_, lean_object* v_a_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3891_, v_b_3892_, v___y_3894_, v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3898_, lean_object* v_as_x27_3899_, lean_object* v_b_3900_, lean_object* v_a_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3898_, v_as_x27_3899_, v_b_3900_, v_a_3901_, v___y_3902_, v___y_3903_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v_as_x27_3899_);
lean_dec(v_as_3898_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3906_, lean_object* v_ref_3907_, lean_object* v_msg_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3907_, v_msg_3908_, v___y_3909_, v___y_3910_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3913_, lean_object* v_ref_3914_, lean_object* v_msg_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3913_, v_ref_3914_, v_msg_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v_ref_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3920_, lean_object* v_m_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3921_, v_a_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3924_, lean_object* v_m_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3924_, v_m_3925_, v_a_3926_);
lean_dec(v_a_3926_);
lean_dec_ref(v_m_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3929_, v_x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3932_, lean_object* v_x_3933_, lean_object* v_x_3934_){
_start:
{
uint8_t v_res_3935_; lean_object* v_r_3936_; 
v_res_3935_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_3932_, v_x_3933_, v_x_3934_);
lean_dec_ref(v_x_3934_);
lean_dec_ref(v_x_3933_);
v_r_3936_ = lean_box(v_res_3935_);
return v_r_3936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3937_, lean_object* v_a_3938_, lean_object* v_x_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_3938_, v_x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3941_, lean_object* v_a_3942_, lean_object* v_x_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_3941_, v_a_3942_, v_x_3943_);
lean_dec(v_x_3943_);
lean_dec(v_a_3942_);
return v_res_3944_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3945_, lean_object* v_x_3946_, size_t v_x_3947_, lean_object* v_x_3948_){
_start:
{
uint8_t v___x_3949_; 
v___x_3949_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_3946_, v_x_3947_, v_x_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_, lean_object* v_x_3953_){
_start:
{
size_t v_x_48083__boxed_3954_; uint8_t v_res_3955_; lean_object* v_r_3956_; 
v_x_48083__boxed_3954_ = lean_unbox_usize(v_x_3952_);
lean_dec(v_x_3952_);
v_res_3955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_3950_, v_x_3951_, v_x_48083__boxed_3954_, v_x_3953_);
lean_dec_ref(v_x_3953_);
lean_dec_ref(v_x_3951_);
v_r_3956_ = lean_box(v_res_3955_);
return v_r_3956_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_3957_, lean_object* v_keys_3958_, lean_object* v_vals_3959_, lean_object* v_heq_3960_, lean_object* v_i_3961_, lean_object* v_k_3962_){
_start:
{
uint8_t v___x_3963_; 
v___x_3963_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_3958_, v_i_3961_, v_k_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3964_, lean_object* v_keys_3965_, lean_object* v_vals_3966_, lean_object* v_heq_3967_, lean_object* v_i_3968_, lean_object* v_k_3969_){
_start:
{
uint8_t v_res_3970_; lean_object* v_r_3971_; 
v_res_3970_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_3964_, v_keys_3965_, v_vals_3966_, v_heq_3967_, v_i_3968_, v_k_3969_);
lean_dec_ref(v_k_3969_);
lean_dec_ref(v_vals_3966_);
lean_dec_ref(v_keys_3965_);
v_r_3971_ = lean_box(v_res_3970_);
return v_r_3971_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_k_3978_){
_start:
{
lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_3980_ = lean_name_eq(v_k_3978_, v___x_3979_);
if (v___x_3980_ == 0)
{
uint8_t v___x_3981_; 
v___x_3981_ = 1;
return v___x_3981_;
}
else
{
uint8_t v___x_3982_; 
v___x_3982_ = 0;
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_k_3983_){
_start:
{
uint8_t v_res_3984_; lean_object* v_r_3985_; 
v_res_3984_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_3983_);
lean_dec(v_k_3983_);
v_r_3985_ = lean_box(v_res_3984_);
return v_r_3985_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_3996_ = l_String_toRawSubstring_x27(v___x_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v___f_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___f_4003_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_4004_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_4004_, 0, v_stx_3999_);
lean_closure_set(v___x_4004_, 1, v___f_4003_);
v___x_4005_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_4004_, v_a_4000_, v_a_4001_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc_n(v_a_4006_, 2);
lean_dec_ref_known(v___x_4005_, 1);
v___x_4007_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_4008_ = l_Lean_Syntax_isOfKind(v_a_4006_, v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v_a_4006_);
v___x_4009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4018_ = lean_unsigned_to_nat(0u);
v___x_4019_ = l_Lean_Syntax_getArg(v_a_4006_, v___x_4018_);
v___x_4020_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4019_);
v___x_4021_ = l_Lean_Syntax_matchesNull(v___x_4019_, v___x_4020_);
if (v___x_4021_ == 0)
{
uint8_t v___x_4022_; 
v___x_4022_ = l_Lean_Syntax_matchesNull(v___x_4019_, v___x_4018_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec(v_a_4006_);
v___x_4023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
else
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_Elab_Command_getRef___redArg(v_a_4000_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4000_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v_quotContext_x3f_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v_a_4041_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v_quotContext_x3f_4036_ = lean_ctor_get(v_a_4000_, 5);
v___x_4037_ = lean_unsigned_to_nat(1u);
v___x_4038_ = l_Lean_Syntax_getArg(v_a_4006_, v___x_4037_);
lean_dec(v_a_4006_);
v___x_4039_ = l_Lean_SourceInfo_fromRef(v_a_4033_, v___x_4021_);
lean_dec(v_a_4033_);
if (lean_obj_tag(v_quotContext_x3f_4036_) == 0)
{
lean_object* v___x_4049_; lean_object* v_a_4050_; 
v___x_4049_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_4001_);
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref(v___x_4049_);
v_a_4041_ = v_a_4050_;
goto v___jp_4040_;
}
else
{
lean_object* v_val_4051_; 
v_val_4051_ = lean_ctor_get(v_quotContext_x3f_4036_, 0);
lean_inc(v_val_4051_);
v_a_4041_ = v_val_4051_;
goto v___jp_4040_;
}
v___jp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4042_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_4044_ = l_Lean_addMacroScope(v_a_4041_, v___x_4043_, v_a_4035_);
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4039_);
lean_ctor_set(v___x_4046_, 1, v___x_4042_);
lean_ctor_set(v___x_4046_, 2, v___x_4044_);
lean_ctor_set(v___x_4046_, 3, v___x_4045_);
v___x_4047_ = lean_box(0);
v___x_4048_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4047_, v___x_4046_, v___x_4038_, v_a_4000_, v_a_4001_);
return v___x_4048_;
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec(v_a_4033_);
lean_dec(v_a_4006_);
v_a_4052_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4034_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4034_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v_a_4006_);
v_a_4060_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4032_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4032_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
else
{
lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4068_ = l_Lean_Syntax_getArg(v___x_4019_, v___x_4018_);
lean_dec(v___x_4019_);
v___x_4069_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_4068_);
v___x_4070_ = l_Lean_Syntax_isOfKind(v___x_4068_, v___x_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
lean_dec(v___x_4068_);
lean_dec(v_a_4006_);
v___x_4071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4071_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4071_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4080_ = lean_unsigned_to_nat(1u);
v___x_4081_ = l_Lean_Syntax_getArg(v_a_4006_, v___x_4080_);
lean_dec(v_a_4006_);
lean_inc(v___x_4068_);
v___x_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4068_);
v___x_4083_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4082_, v___x_4068_, v___x_4081_, v_a_4000_, v_a_4001_);
return v___x_4083_;
}
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_a_4084_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4005_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4005_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Elab_Command_expandMacroArg(v_stx_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
return v_res_4096_;
}
}
lean_object* runtime_initialize_Lean_Elab_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
