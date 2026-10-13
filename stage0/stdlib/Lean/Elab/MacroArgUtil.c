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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1_value;
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_x_9_, v_x_10_);
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
v___x_34_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_32_, v___x_33_);
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
uint8_t v___x_15301__boxed_65_; uint8_t v___x_15302__boxed_66_; lean_object* v_res_67_; 
v___x_15301__boxed_65_ = lean_unbox(v___x_59_);
v___x_15302__boxed_66_ = lean_unbox(v___x_60_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_57_, v___x_58_, v___x_15301__boxed_65_, v___x_15302__boxed_66_, v_x_61_, v___y_62_, v___y_63_);
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
v___x_137_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_135_, v___x_136_);
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
uint8_t v___x_15429__boxed_176_; size_t v_i_boxed_177_; size_t v_stop_boxed_178_; lean_object* v_res_179_; 
v___x_15429__boxed_176_ = lean_unbox(v___x_168_);
v_i_boxed_177_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_171_);
lean_dec(v_stop_171_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_15429__boxed_176_, v_as_169_, v_i_boxed_177_, v_stop_boxed_178_, v_b_172_, v___y_173_, v___y_174_);
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
v___x_227_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_225_, v___x_226_);
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
uint8_t v___x_15623__boxed_265_; size_t v_i_boxed_266_; size_t v_stop_boxed_267_; lean_object* v_res_268_; 
v___x_15623__boxed_265_ = lean_unbox(v___x_257_);
v_i_boxed_266_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_stop_boxed_267_ = lean_unbox_usize(v_stop_260_);
lean_dec(v_stop_260_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_15623__boxed_265_, v_as_258_, v_i_boxed_266_, v_stop_boxed_267_, v_b_261_, v___y_262_, v___y_263_);
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
v___x_316_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_314_, v___x_315_);
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
uint8_t v___x_15801__boxed_355_; size_t v_i_boxed_356_; size_t v_stop_boxed_357_; lean_object* v_res_358_; 
v___x_15801__boxed_355_ = lean_unbox(v___x_347_);
v_i_boxed_356_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_357_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_15801__boxed_355_, v_as_348_, v_i_boxed_356_, v_stop_boxed_357_, v_b_351_, v___y_352_, v___y_353_);
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
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_scopes_417_; lean_object* v___x_418_; lean_object* v_opts_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_415_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_416_ = lean_st_ref_get(v___y_413_);
v_scopes_417_ = lean_ctor_get(v___x_416_, 2);
lean_inc(v_scopes_417_);
lean_dec(v___x_416_);
v___x_418_ = l_List_head_x21___redArg(v___x_415_, v_scopes_417_);
lean_dec(v_scopes_417_);
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
v___x_447_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_451_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
lean_ctor_set(v___x_453_, 3, v___x_452_);
lean_ctor_set(v___x_453_, 4, v___x_451_);
lean_ctor_set(v___x_453_, 5, v___x_451_);
lean_ctor_set(v___x_453_, 6, v___x_451_);
lean_ctor_set(v___x_453_, 7, v___x_451_);
lean_ctor_set(v___x_453_, 8, v___x_451_);
lean_ctor_set(v___x_453_, 9, v___x_451_);
lean_ctor_set(v___x_453_, 10, v___x_451_);
lean_ctor_set(v___x_453_, 11, v___x_450_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(32u);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_457_ = ((size_t)5ULL);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_unsigned_to_nat(32u);
v___x_460_ = lean_mk_empty_array_with_capacity(v___x_459_);
v___x_461_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_462_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_458_);
lean_ctor_set(v___x_462_, 3, v___x_458_);
lean_ctor_set_usize(v___x_462_, 4, v___x_457_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_463_ = lean_box(1);
v___x_464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_465_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_463_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; lean_object* v_env_471_; uint8_t v___x_472_; lean_object* v_env_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_scopes_476_; lean_object* v___x_477_; lean_object* v_opts_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_470_ = lean_st_ref_get(v___y_468_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref(v_env_471_);
lean_dec(v___x_470_);
v___x_472_ = 0;
v_env_473_ = l_Lean_Environment_setRecordingDeps(v_env_471_, v___x_472_);
v___x_474_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_475_ = lean_st_ref_get(v___y_468_);
v_scopes_476_ = lean_ctor_get(v___x_475_, 2);
lean_inc(v_scopes_476_);
lean_dec(v___x_475_);
v___x_477_ = l_List_head_x21___redArg(v___x_474_, v_scopes_476_);
lean_dec(v_scopes_476_);
v_opts_478_ = lean_ctor_get(v___x_477_, 1);
lean_inc_ref(v_opts_478_);
lean_dec(v___x_477_);
v___x_479_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_480_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_481_, 0, v_env_473_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_ctor_set(v___x_481_, 3, v_opts_478_);
v___x_482_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_msgData_467_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Elab_Command_getRef___redArg(v___y_489_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v_macroStack_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v_macroStack_494_ = lean_ctor_get(v___y_489_, 4);
v___x_495_ = l_Lean_Elab_getBetterRef(v_a_493_, v_macroStack_494_);
lean_dec(v_a_493_);
v___x_496_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_488_, v___y_490_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
lean_inc(v_macroStack_494_);
v___x_498_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_497_, v_macroStack_494_, v___y_490_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_495_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_msg_488_);
v_a_508_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_492_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_492_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t v___x_521_, lean_object* v_as_522_, size_t v_i_523_, size_t v_stop_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_a_530_; uint8_t v___x_534_; 
v___x_534_ = lean_usize_dec_eq(v_i_523_, v_stop_524_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v_a_540_; lean_object* v___y_542_; uint8_t v___x_553_; 
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_536_ = lean_array_uget_borrowed(v_as_522_, v_i_523_);
lean_inc(v___x_536_);
v___x_553_ = l_Lean_Syntax_isOfKind(v___x_536_, v___x_535_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_536_);
v___x_555_ = l_Lean_Syntax_isOfKind(v___x_536_, v___x_554_);
if (v___x_555_ == 0)
{
goto v___jp_537_;
}
else
{
lean_object* v___x_556_; lean_object* v_id_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v_id_557_ = l_Lean_Syntax_getArg(v___x_536_, v___x_556_);
if (v___x_553_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_557_);
v___x_583_ = l_Lean_Syntax_isOfKind(v_id_557_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v_id_557_);
goto v___jp_537_;
}
else
{
goto v___jp_558_;
}
}
else
{
goto v___jp_558_;
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_unsigned_to_nat(2u);
v___x_561_ = l_Lean_Syntax_getArg(v___x_536_, v___x_560_);
v___x_562_ = l_Lean_Syntax_matchesNull(v___x_561_, v___x_559_);
if (v___x_562_ == 0)
{
lean_dec(v_id_557_);
goto v___jp_537_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = l_Lean_TSyntax_getId(v_id_557_);
lean_dec(v_id_557_);
v___x_564_ = l_Lean_Parser_getParserAliasInfo(v___x_563_);
lean_dec(v___x_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v_stackSz_x3f_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v_stackSz_x3f_566_ = lean_ctor_get(v_a_565_, 1);
lean_inc(v_stackSz_x3f_566_);
lean_dec(v_a_565_);
v___x_567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_568_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_566_, v___x_567_);
lean_dec(v_stackSz_x3f_566_);
if (v___x_568_ == 0)
{
v_a_540_ = v___x_562_;
goto v___jp_539_;
}
else
{
v_a_540_ = v___x_553_;
goto v___jp_539_;
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_b_525_);
v_a_569_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_581_ == 0)
{
v___x_571_ = v___x_564_;
v_isShared_572_ = v_isSharedCheck_581_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_564_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_581_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_ref_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v_ref_573_ = lean_ctor_get(v___y_526_, 7);
v___x_574_ = lean_io_error_to_string(v_a_569_);
v___x_575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = l_Lean_MessageData_ofFormat(v___x_575_);
lean_inc(v_ref_573_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_ref_573_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_577_);
v___x_579_ = v___x_571_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_584_; lean_object* v_id_585_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v_id_585_ = l_Lean_Syntax_getArg(v___x_536_, v___x_584_);
if (v___x_521_ == 0)
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_585_);
v___x_599_ = l_Lean_Syntax_isOfKind(v_id_585_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v_id_585_);
goto v___jp_537_;
}
else
{
goto v___jp_586_;
}
}
else
{
goto v___jp_586_;
}
v___jp_586_:
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = l_Lean_Syntax_getArg(v___x_536_, v___x_587_);
v___x_589_ = l_Lean_Syntax_isNone(v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
lean_inc(v___x_588_);
v___x_590_ = l_Lean_Syntax_matchesNull(v___x_588_, v___x_587_);
if (v___x_590_ == 0)
{
lean_dec(v___x_588_);
lean_dec(v_id_585_);
goto v___jp_537_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = l_Lean_Syntax_getArg(v___x_588_, v___x_584_);
lean_dec(v___x_588_);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_593_ = l_Lean_Syntax_isOfKind(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v_id_585_);
goto v___jp_537_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(0);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_585_, v___x_584_, v___x_553_, v___x_521_, v___x_594_, v___y_526_, v___y_527_);
lean_dec(v_id_585_);
v___y_542_ = v___x_595_;
goto v___jp_541_;
}
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v___x_588_);
v___x_596_ = lean_box(0);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_585_, v___x_584_, v___x_553_, v___x_521_, v___x_596_, v___y_526_, v___y_527_);
lean_dec(v_id_585_);
v___y_542_ = v___x_597_;
goto v___jp_541_;
}
}
}
v___jp_537_:
{
lean_object* v___x_538_; 
lean_inc(v___x_536_);
v___x_538_ = lean_array_push(v_b_525_, v___x_536_);
v_a_530_ = v___x_538_;
goto v___jp_529_;
}
v___jp_539_:
{
if (v_a_540_ == 0)
{
v_a_530_ = v_b_525_;
goto v___jp_529_;
}
else
{
goto v___jp_537_;
}
}
v___jp_541_:
{
if (lean_obj_tag(v___y_542_) == 0)
{
lean_object* v_a_543_; uint8_t v___x_544_; 
v_a_543_ = lean_ctor_get(v___y_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___y_542_, 1);
v___x_544_ = lean_unbox(v_a_543_);
lean_dec(v_a_543_);
v_a_540_ = v___x_544_;
goto v___jp_539_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_b_525_);
v_a_545_ = lean_ctor_get(v___y_542_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___y_542_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___y_542_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___y_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_b_525_);
return v___x_600_;
}
v___jp_529_:
{
size_t v___x_531_; size_t v___x_532_; 
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_523_, v___x_531_);
v_i_523_ = v___x_532_;
v_b_525_ = v_a_530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v___x_601_, lean_object* v_as_602_, lean_object* v_i_603_, lean_object* v_stop_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___x_16294__boxed_609_; size_t v_i_boxed_610_; size_t v_stop_boxed_611_; lean_object* v_res_612_; 
v___x_16294__boxed_609_ = lean_unbox(v___x_601_);
v_i_boxed_610_ = lean_unbox_usize(v_i_603_);
lean_dec(v_i_603_);
v_stop_boxed_611_ = lean_unbox_usize(v_stop_604_);
lean_dec(v_stop_604_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_16294__boxed_609_, v_as_602_, v_i_boxed_610_, v_stop_boxed_611_, v_b_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v_as_602_);
return v_res_612_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(0);
v___x_626_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_634_);
v___x_642_ = l_Lean_Syntax_isOfKind(v_a_634_, v___x_641_);
v___x_643_ = 1;
if (v___x_642_ == 0)
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_634_);
v___x_651_ = l_Lean_Syntax_isOfKind(v_a_634_, v___x_650_);
if (v___x_651_ == 0)
{
lean_dec(v_a_634_);
goto v___jp_644_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_a_657_; lean_object* v___y_663_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = l_Lean_Syntax_getArg(v_a_634_, v___x_652_);
lean_dec(v_a_634_);
v___x_654_ = l_Lean_Syntax_getArgs(v___x_653_);
lean_dec(v___x_653_);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_array_get_size(v___x_654_);
v___x_674_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_675_ = lean_nat_dec_lt(v___x_655_, v___x_673_);
if (v___x_675_ == 0)
{
lean_dec_ref(v___x_654_);
v_a_657_ = v___x_674_;
goto v___jp_656_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_le(v___x_673_, v___x_673_);
if (v___x_676_ == 0)
{
if (v___x_675_ == 0)
{
lean_dec_ref(v___x_654_);
v_a_657_ = v___x_674_;
goto v___jp_656_;
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_673_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_642_, v___x_654_, v___x_677_, v___x_678_, v___x_674_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_654_);
v___y_663_ = v___x_679_;
goto v___jp_662_;
}
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_673_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_642_, v___x_654_, v___x_680_, v___x_681_, v___x_674_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_654_);
v___y_663_ = v___x_682_;
goto v___jp_662_;
}
}
v___jp_656_:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_array_get_size(v_a_657_);
v___x_659_ = lean_nat_dec_eq(v___x_658_, v___x_652_);
if (v___x_659_ == 0)
{
lean_dec_ref(v_a_657_);
goto v___jp_644_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = lean_array_fget(v_a_657_, v___x_655_);
lean_dec_ref(v_a_657_);
v_a_634_ = v___x_660_;
goto _start;
}
}
v___jp_662_:
{
if (lean_obj_tag(v___y_663_) == 0)
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___y_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___y_663_, 1);
v_a_657_ = v_a_664_;
goto v___jp_656_;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_a_635_);
v_a_665_ = lean_ctor_get(v___y_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___y_663_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___y_663_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___y_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___y_695_; lean_object* v___y_701_; lean_object* v_id_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v_id_711_ = l_Lean_Syntax_getArg(v_a_634_, v___x_683_);
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_713_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_711_);
v___x_714_ = l_Lean_Syntax_isOfKind(v_id_711_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; uint8_t v___x_716_; 
lean_dec(v_id_711_);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_634_);
v___x_716_ = l_Lean_Syntax_isOfKind(v_a_634_, v___x_715_);
if (v___x_716_ == 0)
{
lean_dec(v_a_634_);
goto v___jp_706_;
}
else
{
lean_object* v___x_717_; lean_object* v_a_719_; lean_object* v___y_725_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_735_ = l_Lean_Syntax_getArg(v_a_634_, v___x_717_);
lean_dec(v_a_634_);
v___x_736_ = l_Lean_Syntax_getArgs(v___x_735_);
lean_dec(v___x_735_);
v___x_737_ = lean_array_get_size(v___x_736_);
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_739_ = lean_nat_dec_lt(v___x_683_, v___x_737_);
if (v___x_739_ == 0)
{
lean_dec_ref(v___x_736_);
v_a_719_ = v___x_738_;
goto v___jp_718_;
}
else
{
uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_le(v___x_737_, v___x_737_);
if (v___x_740_ == 0)
{
if (v___x_739_ == 0)
{
lean_dec_ref(v___x_736_);
v_a_719_ = v___x_738_;
goto v___jp_718_;
}
else
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_737_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_714_, v___x_736_, v___x_741_, v___x_742_, v___x_738_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_736_);
v___y_725_ = v___x_743_;
goto v___jp_724_;
}
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_737_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_714_, v___x_736_, v___x_744_, v___x_745_, v___x_738_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_736_);
v___y_725_ = v___x_746_;
goto v___jp_724_;
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
goto v___jp_706_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_array_fget(v_a_719_, v___x_683_);
lean_dec_ref(v_a_719_);
v_a_634_ = v___x_722_;
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
lean_dec(v_a_635_);
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
}
}
else
{
lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___x_829_; lean_object* v_a_831_; lean_object* v___y_837_; lean_object* v_a_848_; lean_object* v___y_854_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_864_ = l_Lean_Syntax_getArg(v_a_634_, v___x_829_);
v___x_865_ = l_Lean_Syntax_isNone(v___x_864_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; 
lean_inc(v___x_864_);
v___x_866_ = l_Lean_Syntax_matchesNull(v___x_864_, v___x_829_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; uint8_t v___x_868_; 
lean_dec(v_id_711_);
v___x_867_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_868_ = l_Lean_Syntax_isOfKind(v_a_634_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec(v___x_864_);
goto v___jp_689_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_869_ = l_Lean_Syntax_getArgs(v___x_864_);
lean_dec(v___x_864_);
v___x_870_ = lean_array_get_size(v___x_869_);
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_872_ = lean_nat_dec_lt(v___x_683_, v___x_870_);
if (v___x_872_ == 0)
{
lean_dec_ref(v___x_869_);
v_a_848_ = v___x_871_;
goto v___jp_847_;
}
else
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_le(v___x_870_, v___x_870_);
if (v___x_873_ == 0)
{
if (v___x_872_ == 0)
{
lean_dec_ref(v___x_869_);
v_a_848_ = v___x_871_;
goto v___jp_847_;
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_870_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_866_, v___x_869_, v___x_874_, v___x_875_, v___x_871_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_869_);
v___y_854_ = v___x_876_;
goto v___jp_853_;
}
}
else
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((size_t)0ULL);
v___x_878_ = lean_usize_of_nat(v___x_870_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_866_, v___x_869_, v___x_877_, v___x_878_, v___x_871_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_869_);
v___y_854_ = v___x_879_;
goto v___jp_853_;
}
}
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = l_Lean_Syntax_getArg(v___x_864_, v___x_683_);
v___x_881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_882_ = l_Lean_Syntax_isOfKind(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; uint8_t v___x_884_; 
lean_dec(v_id_711_);
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_884_ = l_Lean_Syntax_isOfKind(v_a_634_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec(v___x_864_);
goto v___jp_684_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_885_ = l_Lean_Syntax_getArgs(v___x_864_);
lean_dec(v___x_864_);
v___x_886_ = lean_array_get_size(v___x_885_);
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_888_ = lean_nat_dec_lt(v___x_683_, v___x_886_);
if (v___x_888_ == 0)
{
lean_dec_ref(v___x_885_);
v_a_831_ = v___x_887_;
goto v___jp_830_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = lean_nat_dec_le(v___x_886_, v___x_886_);
if (v___x_889_ == 0)
{
if (v___x_888_ == 0)
{
lean_dec_ref(v___x_885_);
v_a_831_ = v___x_887_;
goto v___jp_830_;
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_886_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_882_, v___x_885_, v___x_890_, v___x_891_, v___x_887_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_885_);
v___y_837_ = v___x_892_;
goto v___jp_836_;
}
}
else
{
size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((size_t)0ULL);
v___x_894_ = lean_usize_of_nat(v___x_886_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_882_, v___x_885_, v___x_893_, v___x_894_, v___x_887_, v_a_636_, v_a_637_);
lean_dec_ref(v___x_885_);
v___y_837_ = v___x_895_;
goto v___jp_836_;
}
}
}
}
else
{
lean_dec(v___x_864_);
lean_dec(v_a_634_);
v___y_748_ = v_a_636_;
v___y_749_ = v_a_637_;
goto v___jp_747_;
}
}
}
else
{
lean_dec(v___x_864_);
lean_dec(v_a_634_);
v___y_748_ = v_a_636_;
v___y_749_ = v_a_637_;
goto v___jp_747_;
}
v___jp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc(v_id_711_);
v___x_750_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_750_, 0, v_id_711_);
v___x_751_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_750_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_820_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_820_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_820_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_820_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
if (lean_obj_tag(v_a_752_) == 1)
{
lean_object* v_val_756_; 
v_val_756_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v_a_752_, 1);
switch(lean_obj_tag(v_val_756_))
{
case 0:
{
lean_object* v_cat_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_id_711_);
v_cat_757_ = lean_ctor_get(v_val_756_, 0);
lean_inc(v_cat_757_);
lean_dec_ref_known(v_val_756_, 1);
v___x_758_ = lean_box(0);
v___x_759_ = l_Lean_Syntax_mkAntiquotNode(v_cat_757_, v_a_635_, v___x_683_, v___x_758_, v___x_643_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_759_);
v___x_761_ = v___x_754_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
case 1:
{
lean_object* v_decl_763_; 
lean_del_object(v___x_754_);
lean_dec(v_id_711_);
v_decl_763_ = lean_ctor_get(v_val_756_, 0);
lean_inc(v_decl_763_);
lean_dec_ref_known(v_val_756_, 1);
if (lean_obj_tag(v_decl_763_) == 1)
{
lean_object* v_pre_764_; 
v_pre_764_ = lean_ctor_get(v_decl_763_, 0);
if (lean_obj_tag(v_pre_764_) == 1)
{
lean_object* v_pre_765_; 
v_pre_765_ = lean_ctor_get(v_pre_764_, 0);
if (lean_obj_tag(v_pre_765_) == 1)
{
lean_object* v_pre_766_; 
v_pre_766_ = lean_ctor_get(v_pre_765_, 0);
switch(lean_obj_tag(v_pre_766_))
{
case 0:
{
lean_object* v_str_767_; lean_object* v_str_768_; lean_object* v_str_769_; uint8_t v___x_770_; 
v_str_767_ = lean_ctor_get(v_decl_763_, 1);
v_str_768_ = lean_ctor_get(v_pre_764_, 1);
v_str_769_ = lean_ctor_get(v_pre_765_, 1);
v___x_770_ = lean_string_dec_eq(v_str_769_, v___x_639_);
if (v___x_770_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = lean_string_dec_eq(v_str_768_, v___x_640_);
if (v___x_771_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_string_dec_eq(v_str_767_, v___x_712_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_774_ = lean_string_dec_eq(v_str_767_, v___x_773_);
if (v___x_774_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
lean_object* v___x_775_; 
lean_dec_ref_known(v_decl_763_, 2);
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_695_ = v___x_775_;
goto v___jp_694_;
}
}
else
{
lean_object* v___x_776_; 
lean_dec_ref_known(v_decl_763_, 2);
v___x_776_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_695_ = v___x_776_;
goto v___jp_694_;
}
}
}
}
case 1:
{
lean_object* v_pre_777_; 
v_pre_777_ = lean_ctor_get(v_pre_766_, 0);
if (lean_obj_tag(v_pre_777_) == 0)
{
lean_object* v_str_778_; lean_object* v_str_779_; lean_object* v_str_780_; lean_object* v_str_781_; uint8_t v___x_782_; 
v_str_778_ = lean_ctor_get(v_decl_763_, 1);
v_str_779_ = lean_ctor_get(v_pre_764_, 1);
v_str_780_ = lean_ctor_get(v_pre_765_, 1);
v_str_781_ = lean_ctor_get(v_pre_766_, 1);
v___x_782_ = lean_string_dec_eq(v_str_781_, v___x_639_);
if (v___x_782_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_string_dec_eq(v_str_780_, v___x_640_);
if (v___x_783_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_785_ = lean_string_dec_eq(v_str_779_, v___x_784_);
if (v___x_785_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_string_dec_eq(v_str_778_, v___x_712_);
if (v___x_786_ == 0)
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
else
{
lean_object* v___x_787_; 
lean_dec_ref_known(v_decl_763_, 2);
v___x_787_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_695_ = v___x_787_;
goto v___jp_694_;
}
}
}
}
}
else
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
}
default: 
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
}
}
else
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
}
else
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
}
else
{
v___y_695_ = v_decl_763_;
goto v___jp_694_;
}
}
default: 
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_812_; 
lean_del_object(v___x_754_);
v_isSharedCheck_812_ = !lean_is_exclusive(v_val_756_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_val_756_, 0);
lean_dec(v_unused_813_);
v___x_789_ = v_val_756_;
v_isShared_790_ = v_isSharedCheck_812_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_val_756_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_812_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = l_Lean_TSyntax_getId(v_id_711_);
lean_dec(v_id_711_);
v___x_792_ = l_Lean_Name_eraseMacroScopes(v___x_791_);
lean_dec(v___x_791_);
v___x_793_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_792_);
lean_dec(v___x_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; 
lean_del_object(v___x_789_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
if (lean_obj_tag(v_a_794_) == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_box(0);
v___y_701_ = v___x_795_;
goto v___jp_700_;
}
else
{
lean_object* v_val_796_; 
v_val_796_ = lean_ctor_get(v_a_794_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v_a_794_, 1);
v___y_701_ = v_val_796_;
goto v___jp_700_;
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_635_);
v_a_797_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_811_ == 0)
{
v___x_799_ = v___x_793_;
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_793_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_ref_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v_ref_801_ = lean_ctor_get(v___y_748_, 7);
v___x_802_ = lean_io_error_to_string(v_a_797_);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 3);
lean_ctor_set(v___x_789_, 0, v___x_802_);
v___x_804_ = v___x_789_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_810_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_805_ = l_Lean_MessageData_ofFormat(v___x_804_);
lean_inc(v_ref_801_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_ref_801_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
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
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_del_object(v___x_754_);
lean_dec(v_a_752_);
lean_dec(v_a_635_);
v___x_814_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_815_ = l_Lean_MessageData_ofSyntax(v_id_711_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_818_, v___y_748_, v___y_749_);
return v___x_819_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_id_711_);
lean_dec(v_a_635_);
v_a_821_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_751_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_751_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
v___jp_830_:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_array_get_size(v_a_831_);
v___x_833_ = lean_nat_dec_eq(v___x_832_, v___x_829_);
if (v___x_833_ == 0)
{
lean_dec_ref(v_a_831_);
goto v___jp_684_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = lean_array_fget(v_a_831_, v___x_683_);
lean_dec_ref(v_a_831_);
v_a_634_ = v___x_834_;
goto _start;
}
}
v___jp_836_:
{
if (lean_obj_tag(v___y_837_) == 0)
{
lean_object* v_a_838_; 
v_a_838_ = lean_ctor_get(v___y_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___y_837_, 1);
v_a_831_ = v_a_838_;
goto v___jp_830_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_a_635_);
v_a_839_ = lean_ctor_get(v___y_837_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___y_837_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___y_837_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___y_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
v___jp_847_:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_a_848_);
v___x_850_ = lean_nat_dec_eq(v___x_849_, v___x_829_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_a_848_);
goto v___jp_689_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_array_fget(v_a_848_, v___x_683_);
lean_dec_ref(v_a_848_);
v_a_634_ = v___x_851_;
goto _start;
}
}
v___jp_853_:
{
if (lean_obj_tag(v___y_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___y_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___y_854_, 1);
v_a_848_ = v_a_855_;
goto v___jp_847_;
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_635_);
v_a_856_ = lean_ctor_get(v___y_854_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___y_854_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___y_854_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___y_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_box(0);
v___x_686_ = lean_box(0);
v___x_687_ = l_Lean_Syntax_mkAntiquotNode(v___x_685_, v_a_635_, v___x_683_, v___x_686_, v___x_643_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
v___jp_689_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_box(0);
v___x_691_ = lean_box(0);
v___x_692_ = l_Lean_Syntax_mkAntiquotNode(v___x_690_, v_a_635_, v___x_683_, v___x_691_, v___x_643_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
v___jp_694_:
{
lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_696_ = lean_box(0);
v___x_697_ = 0;
v___x_698_ = l_Lean_Syntax_mkAntiquotNode(v___y_695_, v_a_635_, v___x_683_, v___x_696_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
v___jp_700_:
{
lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = lean_box(0);
v___x_703_ = 0;
v___x_704_ = l_Lean_Syntax_mkAntiquotNode(v___y_701_, v_a_635_, v___x_683_, v___x_702_, v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
v___jp_706_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_box(0);
v___x_709_ = l_Lean_Syntax_mkAntiquotNode(v___x_707_, v_a_635_, v___x_683_, v___x_708_, v___x_643_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_645_ = lean_box(0);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_box(0);
v___x_648_ = l_Lean_Syntax_mkAntiquotNode(v___x_645_, v_a_635_, v___x_646_, v___x_647_, v___x_643_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_902_, v___y_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_912_, lean_object* v_msg_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_913_, v___y_914_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_918_, lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_918_, v_msg_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_924_, lean_object* v_macroStack_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_924_, v_macroStack_925_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_930_, lean_object* v_macroStack_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_930_, v_macroStack_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_939_, lean_object* v_stx_940_, lean_object* v_id_941_, lean_object* v_suffix_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_940_, v_id_941_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_961_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_961_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_961_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_961_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_951_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_939_, v_a_947_, v_suffix_942_);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_array_push(v___x_953_, v___x_951_);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_956_ = lean_box(2);
v___x_957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_954_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_957_);
v___x_959_ = v___x_949_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_dec_ref(v_suffix_942_);
lean_dec(v_kind_939_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_962_, lean_object* v_stx_963_, lean_object* v_id_964_, lean_object* v_suffix_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_962_, v_stx_963_, v_id_964_, v_suffix_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; lean_object* v_env_973_; lean_object* v___x_974_; lean_object* v_mainModule_975_; lean_object* v___x_976_; 
v___x_972_ = lean_st_ref_get(v___y_970_);
v_env_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc_ref(v_env_973_);
lean_dec(v___x_972_);
v___x_974_ = l_Lean_Environment_header(v_env_973_);
lean_dec_ref(v_env_973_);
v_mainModule_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_mainModule_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_mainModule_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_977_);
lean_dec(v___y_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_991_ = lean_panic_fn_borrowed(v___x_990_, v_msg_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = l_Lean_maxRecDepthErrorMessage;
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_1000_ = l_Lean_MessageData_ofFormat(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_1002_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_1003_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_ref_1004_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_1012_, lean_object* v_declName_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1016_; lean_object* v_env_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; uint8_t v___x_1020_; 
v___x_1016_ = 0;
v_env_1017_ = l_Lean_Environment_setExporting(v_env_1012_, v___x_1016_);
lean_inc(v_declName_1013_);
v___x_1018_ = l_Lean_mkPrivateName(v_env_1017_, v_declName_1013_);
v___x_1019_ = 1;
lean_inc_ref(v_env_1017_);
v___x_1020_ = l_Lean_Environment_contains(v_env_1017_, v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = l_Lean_privateToUserName(v_declName_1013_);
v___x_1022_ = l_Lean_Environment_contains(v_env_1017_, v___x_1021_, v___x_1019_);
v___x_1023_ = lean_box(v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___y_1015_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec_ref(v_env_1017_);
lean_dec(v_declName_1013_);
v___x_1025_ = lean_box(v___x_1020_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___y_1015_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_1027_, lean_object* v_declName_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1027_, v_declName_1028_, v___y_1029_, v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_1032_, lean_object* v_i_1033_, lean_object* v_k_1034_){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_array_get_size(v_keys_1032_);
v___x_1036_ = lean_nat_dec_lt(v_i_1033_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_dec(v_i_1033_);
return v___x_1036_;
}
else
{
lean_object* v_k_x27_1037_; uint8_t v___x_1038_; 
v_k_x27_1037_ = lean_array_fget_borrowed(v_keys_1032_, v_i_1033_);
v___x_1038_ = l_Lean_instBEqExtraModUse_beq(v_k_1034_, v_k_x27_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_i_1033_, v___x_1039_);
lean_dec(v_i_1033_);
v_i_1033_ = v___x_1040_;
goto _start;
}
else
{
lean_dec(v_i_1033_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
uint8_t v_res_1045_; lean_object* v_r_1046_; 
v_res_1045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_1042_, v_i_1043_, v_k_1044_);
lean_dec_ref(v_k_1044_);
lean_dec_ref(v_keys_1042_);
v_r_1046_ = lean_box(v_res_1045_);
return v_r_1046_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_1047_, size_t v_x_1048_, lean_object* v_x_1049_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v_es_1050_; lean_object* v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; lean_object* v_j_1054_; lean_object* v___x_1055_; 
v_es_1050_ = lean_ctor_get(v_x_1047_, 0);
v___x_1051_ = lean_box(2);
v___x_1052_ = ((size_t)31ULL);
v___x_1053_ = lean_usize_land(v_x_1048_, v___x_1052_);
v_j_1054_ = lean_usize_to_nat(v___x_1053_);
v___x_1055_ = lean_array_get_borrowed(v___x_1051_, v_es_1050_, v_j_1054_);
lean_dec(v_j_1054_);
switch(lean_obj_tag(v___x_1055_))
{
case 0:
{
lean_object* v_key_1056_; uint8_t v___x_1057_; 
v_key_1056_ = lean_ctor_get(v___x_1055_, 0);
v___x_1057_ = l_Lean_instBEqExtraModUse_beq(v_x_1049_, v_key_1056_);
return v___x_1057_;
}
case 1:
{
lean_object* v_node_1058_; size_t v___x_1059_; size_t v___x_1060_; 
v_node_1058_ = lean_ctor_get(v___x_1055_, 0);
v___x_1059_ = ((size_t)5ULL);
v___x_1060_ = lean_usize_shift_right(v_x_1048_, v___x_1059_);
v_x_1047_ = v_node_1058_;
v_x_1048_ = v___x_1060_;
goto _start;
}
default: 
{
uint8_t v___x_1062_; 
v___x_1062_ = 0;
return v___x_1062_;
}
}
}
else
{
lean_object* v_ks_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_ks_1063_ = lean_ctor_get(v_x_1047_, 0);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_1063_, v___x_1064_, v_x_1049_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
size_t v_x_42652__boxed_1069_; uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_x_42652__boxed_1069_ = lean_unbox_usize(v_x_1067_);
lean_dec(v_x_1067_);
v_res_1070_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1066_, v_x_42652__boxed_1069_, v_x_1068_);
lean_dec_ref(v_x_1068_);
lean_dec_ref(v_x_1066_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
uint64_t v___x_1074_; size_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = l_Lean_instHashableExtraModUse_hash(v_x_1073_);
v___x_1075_ = lean_uint64_to_usize(v___x_1074_);
v___x_1076_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1072_, v___x_1075_, v_x_1073_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_1077_, v_x_1078_);
lean_dec_ref(v_x_1078_);
lean_dec_ref(v_x_1077_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1081_; double v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_float_of_nat(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Elab_Command_getRef___redArg(v___y_1087_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1141_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_1086_, v___y_1088_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1141_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1141_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v_traceState_1098_; lean_object* v_env_1099_; lean_object* v_messages_1100_; lean_object* v_scopes_1101_; lean_object* v_usedQuotCtxts_1102_; lean_object* v_nextMacroScope_1103_; lean_object* v_maxRecDepth_1104_; lean_object* v_ngen_1105_; lean_object* v_auxDeclNGen_1106_; lean_object* v_infoState_1107_; lean_object* v_snapshotTasks_1108_; lean_object* v_prevLinterStates_1109_; lean_object* v_codeQualityEntryTasks_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1140_; 
v___x_1097_ = lean_st_ref_take(v___y_1088_);
v_traceState_1098_ = lean_ctor_get(v___x_1097_, 9);
v_env_1099_ = lean_ctor_get(v___x_1097_, 0);
v_messages_1100_ = lean_ctor_get(v___x_1097_, 1);
v_scopes_1101_ = lean_ctor_get(v___x_1097_, 2);
v_usedQuotCtxts_1102_ = lean_ctor_get(v___x_1097_, 3);
v_nextMacroScope_1103_ = lean_ctor_get(v___x_1097_, 4);
v_maxRecDepth_1104_ = lean_ctor_get(v___x_1097_, 5);
v_ngen_1105_ = lean_ctor_get(v___x_1097_, 6);
v_auxDeclNGen_1106_ = lean_ctor_get(v___x_1097_, 7);
v_infoState_1107_ = lean_ctor_get(v___x_1097_, 8);
v_snapshotTasks_1108_ = lean_ctor_get(v___x_1097_, 10);
v_prevLinterStates_1109_ = lean_ctor_get(v___x_1097_, 11);
v_codeQualityEntryTasks_1110_ = lean_ctor_get(v___x_1097_, 12);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1112_ = v___x_1097_;
v_isShared_1113_ = v_isSharedCheck_1140_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1110_);
lean_inc(v_prevLinterStates_1109_);
lean_inc(v_snapshotTasks_1108_);
lean_inc(v_traceState_1098_);
lean_inc(v_infoState_1107_);
lean_inc(v_auxDeclNGen_1106_);
lean_inc(v_ngen_1105_);
lean_inc(v_maxRecDepth_1104_);
lean_inc(v_nextMacroScope_1103_);
lean_inc(v_usedQuotCtxts_1102_);
lean_inc(v_scopes_1101_);
lean_inc(v_messages_1100_);
lean_inc(v_env_1099_);
lean_dec(v___x_1097_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1140_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
uint64_t v_tid_1114_; lean_object* v_traces_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1139_; 
v_tid_1114_ = lean_ctor_get_uint64(v_traceState_1098_, sizeof(void*)*1);
v_traces_1115_ = lean_ctor_get(v_traceState_1098_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_traceState_1098_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1117_ = v_traceState_1098_;
v_isShared_1118_ = v_isSharedCheck_1139_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_traces_1115_);
lean_dec(v_traceState_1098_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1139_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; double v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_1122_ = 0;
v___x_1123_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1124_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1124_, 0, v_cls_1085_);
lean_ctor_set(v___x_1124_, 1, v___x_1120_);
lean_ctor_set(v___x_1124_, 2, v___x_1123_);
lean_ctor_set_float(v___x_1124_, sizeof(void*)*3, v___x_1121_);
lean_ctor_set_float(v___x_1124_, sizeof(void*)*3 + 8, v___x_1121_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*3 + 16, v___x_1122_);
v___x_1125_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_1126_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v_a_1093_);
lean_ctor_set(v___x_1126_, 2, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_a_1091_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_PersistentArray_push___redArg(v_traces_1115_, v___x_1127_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1128_);
v___x_1130_ = v___x_1117_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1128_);
lean_ctor_set_uint64(v_reuseFailAlloc_1138_, sizeof(void*)*1, v_tid_1114_);
v___x_1130_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 9, v___x_1130_);
v___x_1132_ = v___x_1112_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_env_1099_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_messages_1100_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_scopes_1101_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_usedQuotCtxts_1102_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_nextMacroScope_1103_);
lean_ctor_set(v_reuseFailAlloc_1137_, 5, v_maxRecDepth_1104_);
lean_ctor_set(v_reuseFailAlloc_1137_, 6, v_ngen_1105_);
lean_ctor_set(v_reuseFailAlloc_1137_, 7, v_auxDeclNGen_1106_);
lean_ctor_set(v_reuseFailAlloc_1137_, 8, v_infoState_1107_);
lean_ctor_set(v_reuseFailAlloc_1137_, 9, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 10, v_snapshotTasks_1108_);
lean_ctor_set(v_reuseFailAlloc_1137_, 11, v_prevLinterStates_1109_);
lean_ctor_set(v_reuseFailAlloc_1137_, 12, v_codeQualityEntryTasks_1110_);
v___x_1132_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_st_ref_put(v___y_1088_, v___x_1132_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1119_);
v___x_1135_ = v___x_1095_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1119_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_msg_1086_);
lean_dec(v_cls_1085_);
v_a_1142_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1090_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1090_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1150_, lean_object* v_msg_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1150_, v_msg_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0(lean_object* v___x_1156_, lean_object* v_entry_1157_, lean_object* v_s_1158_){
_start:
{
lean_object* v_addEntryFn_1159_; lean_object* v_importedEntries_1160_; lean_object* v_state_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1169_; 
v_addEntryFn_1159_ = lean_ctor_get(v___x_1156_, 3);
lean_inc(v_addEntryFn_1159_);
lean_dec_ref(v___x_1156_);
v_importedEntries_1160_ = lean_ctor_get(v_s_1158_, 0);
v_state_1161_ = lean_ctor_get(v_s_1158_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_s_1158_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1163_ = v_s_1158_;
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_state_1161_);
lean_inc(v_importedEntries_1160_);
lean_dec(v_s_1158_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_state_1165_; lean_object* v___x_1167_; 
v_state_1165_ = lean_apply_2(v_addEntryFn_1159_, v_state_1161_, v_entry_1157_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_state_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_importedEntries_1160_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_state_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1170_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3));
v___x_1176_ = l_Lean_stringToMessageData(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9(void){
_start:
{
lean_object* v_cls_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_cls_1183_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1184_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
v___x_1185_ = l_Lean_Name_append(v___x_1184_, v_cls_1183_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1196_, uint8_t v_isMeta_1197_, lean_object* v_hint_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_env_1223_; uint8_t v_isExporting_1224_; lean_object* v_entry_1225_; lean_object* v___x_1226_; lean_object* v_env_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0);
v___x_1222_ = lean_st_ref_get(v___y_1200_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v_isExporting_1224_ = lean_ctor_get_uint8(v_env_1223_, sizeof(void*)*13);
lean_dec_ref(v_env_1223_);
lean_inc(v_mod_1196_);
v_entry_1225_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1225_, 0, v_mod_1196_);
lean_ctor_set_uint8(v_entry_1225_, sizeof(void*)*1, v_isExporting_1224_);
lean_ctor_set_uint8(v_entry_1225_, sizeof(void*)*1 + 1, v_isMeta_1197_);
v___x_1226_ = lean_st_ref_get(v___y_1200_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1229_ = lean_box(1);
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1221_, v___x_1228_, v_env_1227_, v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1231_, v_entry_1225_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___f_1233_; uint8_t v___x_1234_; lean_object* v___y_1236_; lean_object* v_cls_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v_scopes_1283_; lean_object* v___x_1284_; lean_object* v_opts_1285_; uint8_t v_hasTrace_1286_; 
v___f_1233_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_1233_, 0, v___x_1228_);
lean_closure_set(v___f_1233_, 1, v_entry_1225_);
v___x_1234_ = 1;
v_cls_1258_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1259_ = l_Lean_inheritedTraceOptions;
v___x_1260_ = lean_st_ref_get(v___x_1259_);
v___x_1261_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1262_ = lean_st_ref_get(v___y_1200_);
v_scopes_1283_ = lean_ctor_get(v___x_1262_, 2);
lean_inc(v_scopes_1283_);
lean_dec(v___x_1262_);
v___x_1284_ = l_List_head_x21___redArg(v___x_1261_, v_scopes_1283_);
lean_dec(v_scopes_1283_);
v_opts_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc_ref(v_opts_1285_);
lean_dec(v___x_1284_);
v_hasTrace_1286_ = lean_ctor_get_uint8(v_opts_1285_, sizeof(void*)*1);
if (v_hasTrace_1286_ == 0)
{
lean_dec_ref(v_opts_1285_);
lean_dec(v___x_1260_);
lean_dec(v_hint_1198_);
lean_dec(v_mod_1196_);
v___y_1236_ = v___y_1200_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9);
v___x_1288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1260_, v_opts_1285_, v___x_1287_);
lean_dec_ref(v_opts_1285_);
lean_dec(v___x_1260_);
if (v___x_1288_ == 0)
{
lean_dec(v_hint_1198_);
lean_dec(v_mod_1196_);
v___y_1236_ = v___y_1200_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1289_; lean_object* v___y_1291_; 
v___x_1289_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
if (v_isExporting_1224_ == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1291_ = v___x_1298_;
goto v___jp_1290_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1291_ = v___x_1299_;
goto v___jp_1290_;
}
v___jp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_inc_ref(v___y_1291_);
v___x_1292_ = l_Lean_stringToMessageData(v___y_1291_);
v___x_1293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1289_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
if (v_isMeta_1197_ == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___y_1269_ = v___x_1295_;
v___y_1270_ = v___x_1296_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15));
v___y_1269_ = v___x_1295_;
v___y_1270_ = v___x_1297_;
goto v___jp_1268_;
}
}
}
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v_toEnvExtension_1238_; lean_object* v_env_1239_; lean_object* v_messages_1240_; lean_object* v_scopes_1241_; lean_object* v_usedQuotCtxts_1242_; lean_object* v_nextMacroScope_1243_; lean_object* v_maxRecDepth_1244_; lean_object* v_ngen_1245_; lean_object* v_auxDeclNGen_1246_; lean_object* v_infoState_1247_; lean_object* v_traceState_1248_; lean_object* v_snapshotTasks_1249_; lean_object* v_prevLinterStates_1250_; lean_object* v_codeQualityEntryTasks_1251_; lean_object* v_asyncMode_1252_; uint8_t v_logWrites_1253_; lean_object* v___x_1254_; 
v___x_1237_ = lean_st_ref_take(v___y_1236_);
v_toEnvExtension_1238_ = lean_ctor_get(v___x_1228_, 0);
v_env_1239_ = lean_ctor_get(v___x_1237_, 0);
lean_inc_ref(v_env_1239_);
v_messages_1240_ = lean_ctor_get(v___x_1237_, 1);
lean_inc_ref(v_messages_1240_);
v_scopes_1241_ = lean_ctor_get(v___x_1237_, 2);
lean_inc(v_scopes_1241_);
v_usedQuotCtxts_1242_ = lean_ctor_get(v___x_1237_, 3);
lean_inc(v_usedQuotCtxts_1242_);
v_nextMacroScope_1243_ = lean_ctor_get(v___x_1237_, 4);
lean_inc(v_nextMacroScope_1243_);
v_maxRecDepth_1244_ = lean_ctor_get(v___x_1237_, 5);
lean_inc(v_maxRecDepth_1244_);
v_ngen_1245_ = lean_ctor_get(v___x_1237_, 6);
lean_inc_ref(v_ngen_1245_);
v_auxDeclNGen_1246_ = lean_ctor_get(v___x_1237_, 7);
lean_inc_ref(v_auxDeclNGen_1246_);
v_infoState_1247_ = lean_ctor_get(v___x_1237_, 8);
lean_inc_ref(v_infoState_1247_);
v_traceState_1248_ = lean_ctor_get(v___x_1237_, 9);
lean_inc_ref(v_traceState_1248_);
v_snapshotTasks_1249_ = lean_ctor_get(v___x_1237_, 10);
lean_inc_ref(v_snapshotTasks_1249_);
v_prevLinterStates_1250_ = lean_ctor_get(v___x_1237_, 11);
lean_inc(v_prevLinterStates_1250_);
v_codeQualityEntryTasks_1251_ = lean_ctor_get(v___x_1237_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1251_);
lean_dec(v___x_1237_);
v_asyncMode_1252_ = lean_ctor_get(v_toEnvExtension_1238_, 2);
v_logWrites_1253_ = lean_ctor_get_uint8(v_toEnvExtension_1238_, sizeof(void*)*6);
v___x_1254_ = lean_box(0);
if (v_logWrites_1253_ == 0)
{
lean_object* v___x_1255_; 
lean_inc_ref(v_toEnvExtension_1238_);
v___x_1255_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1238_, v_env_1239_, v___f_1233_, v_asyncMode_1252_, v___x_1230_, v___x_1234_);
v___y_1203_ = v_scopes_1241_;
v___y_1204_ = v_nextMacroScope_1243_;
v___y_1205_ = v_maxRecDepth_1244_;
v___y_1206_ = v_codeQualityEntryTasks_1251_;
v___y_1207_ = v_auxDeclNGen_1246_;
v___y_1208_ = v___y_1236_;
v___y_1209_ = v_usedQuotCtxts_1242_;
v___y_1210_ = v_ngen_1245_;
v___y_1211_ = v_messages_1240_;
v___y_1212_ = v___x_1254_;
v___y_1213_ = v_infoState_1247_;
v___y_1214_ = v_traceState_1248_;
v___y_1215_ = v_prevLinterStates_1250_;
v___y_1216_ = v_snapshotTasks_1249_;
v___y_1217_ = v___x_1255_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref_n(v_toEnvExtension_1238_, 2);
v___x_1256_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1238_, v_env_1239_);
lean_dec_ref(v_env_1239_);
v___x_1257_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1238_, v___x_1256_, v___f_1233_, v_asyncMode_1252_, v___x_1230_, v___x_1234_);
v___y_1203_ = v_scopes_1241_;
v___y_1204_ = v_nextMacroScope_1243_;
v___y_1205_ = v_maxRecDepth_1244_;
v___y_1206_ = v_codeQualityEntryTasks_1251_;
v___y_1207_ = v_auxDeclNGen_1246_;
v___y_1208_ = v___y_1236_;
v___y_1209_ = v_usedQuotCtxts_1242_;
v___y_1210_ = v_ngen_1245_;
v___y_1211_ = v_messages_1240_;
v___y_1212_ = v___x_1254_;
v___y_1213_ = v_infoState_1247_;
v___y_1214_ = v_traceState_1248_;
v___y_1215_ = v_prevLinterStates_1250_;
v___y_1216_ = v_snapshotTasks_1249_;
v___y_1217_ = v___x_1257_;
goto v___jp_1202_;
}
}
v___jp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1264_);
lean_ctor_set(v___x_1266_, 1, v___y_1265_);
v___x_1267_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1258_, v___x_1266_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_dec_ref_known(v___x_1267_, 1);
v___y_1236_ = v___y_1200_;
goto v___jp_1235_;
}
else
{
lean_dec_ref(v___f_1233_);
return v___x_1267_;
}
}
v___jp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
lean_inc_ref(v___y_1270_);
v___x_1271_ = l_Lean_stringToMessageData(v___y_1270_);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___y_1269_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_MessageData_ofName(v_mod_1196_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Lean_Name_isAnonymous(v_hint_1198_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1279_ = l_Lean_MessageData_ofName(v_hint_1198_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___y_1264_ = v___x_1276_;
v___y_1265_ = v___x_1280_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v_hint_1198_);
v___x_1281_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
v___y_1264_ = v___x_1276_;
v___y_1265_ = v___x_1282_;
goto v___jp_1263_;
}
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref_known(v_entry_1225_, 1);
lean_dec(v_hint_1198_);
lean_dec(v_mod_1196_);
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
v___jp_1202_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1218_, 0, v___y_1217_);
lean_ctor_set(v___x_1218_, 1, v___y_1211_);
lean_ctor_set(v___x_1218_, 2, v___y_1203_);
lean_ctor_set(v___x_1218_, 3, v___y_1209_);
lean_ctor_set(v___x_1218_, 4, v___y_1204_);
lean_ctor_set(v___x_1218_, 5, v___y_1205_);
lean_ctor_set(v___x_1218_, 6, v___y_1210_);
lean_ctor_set(v___x_1218_, 7, v___y_1207_);
lean_ctor_set(v___x_1218_, 8, v___y_1213_);
lean_ctor_set(v___x_1218_, 9, v___y_1214_);
lean_ctor_set(v___x_1218_, 10, v___y_1216_);
lean_ctor_set(v___x_1218_, 11, v___y_1215_);
lean_ctor_set(v___x_1218_, 12, v___y_1206_);
v___x_1219_ = lean_st_ref_put(v___y_1208_, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1212_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1302_, lean_object* v_isMeta_1303_, lean_object* v_hint_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v_isMeta_boxed_1308_; lean_object* v_res_1309_; 
v_isMeta_boxed_1308_ = lean_unbox(v_isMeta_1303_);
v_res_1309_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1302_, v_isMeta_boxed_1308_, v_hint_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1310_, lean_object* v_declName_1311_, lean_object* v_as_1312_, size_t v_sz_1313_, size_t v_i_1314_, lean_object* v_b_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1314_, v_sz_1313_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_declName_1311_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_b_1315_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v_modules_1322_; lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v_toImport_1326_; lean_object* v_module_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1321_ = l_Lean_Environment_header(v___x_1310_);
v_modules_1322_ = lean_ctor_get(v___x_1321_, 3);
lean_inc_ref(v_modules_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1324_ = lean_array_uget_borrowed(v_as_1312_, v_i_1314_);
v___x_1325_ = lean_array_get(v___x_1323_, v_modules_1322_, v_a_1324_);
lean_dec_ref(v_modules_1322_);
v_toImport_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc_ref(v_toImport_1326_);
lean_dec(v___x_1325_);
v_module_1327_ = lean_ctor_get(v_toImport_1326_, 0);
lean_inc(v_module_1327_);
lean_dec_ref(v_toImport_1326_);
v___x_1328_ = lean_box(0);
v___x_1329_ = 0;
lean_inc(v_declName_1311_);
v___x_1330_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1327_, v___x_1329_, v_declName_1311_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1330_) == 0)
{
size_t v___x_1331_; size_t v___x_1332_; 
lean_dec_ref_known(v___x_1330_, 1);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1314_, v___x_1331_);
v_i_1314_ = v___x_1332_;
v_b_1315_ = v___x_1328_;
goto _start;
}
else
{
lean_dec(v_declName_1311_);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1334_, lean_object* v_declName_1335_, lean_object* v_as_1336_, lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1334_, v_declName_1335_, v_as_1336_, v_sz_boxed_1343_, v_i_boxed_1344_, v_b_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v_as_1336_);
lean_dec_ref(v___x_1334_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1346_, lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
else
{
lean_object* v_key_1349_; lean_object* v_value_1350_; lean_object* v_tail_1351_; uint8_t v___x_1352_; 
v_key_1349_ = lean_ctor_get(v_x_1347_, 0);
v_value_1350_ = lean_ctor_get(v_x_1347_, 1);
v_tail_1351_ = lean_ctor_get(v_x_1347_, 2);
v___x_1352_ = lean_name_eq(v_key_1349_, v_a_1346_);
if (v___x_1352_ == 0)
{
v_x_1347_ = v_tail_1351_;
goto _start;
}
else
{
lean_object* v___x_1354_; 
lean_inc(v_value_1350_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_value_1350_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1355_, v_x_1356_);
lean_dec(v_x_1356_);
lean_dec(v_a_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_buckets_1360_; lean_object* v___x_1361_; uint64_t v___y_1363_; 
v_buckets_1360_ = lean_ctor_get(v_m_1358_, 1);
v___x_1361_ = lean_array_get_size(v_buckets_1360_);
if (lean_obj_tag(v_a_1359_) == 0)
{
uint64_t v___x_1377_; 
v___x_1377_ = 1723ULL;
v___y_1363_ = v___x_1377_;
goto v___jp_1362_;
}
else
{
uint64_t v_hash_1378_; 
v_hash_1378_ = lean_ctor_get_uint64(v_a_1359_, sizeof(void*)*2);
v___y_1363_ = v_hash_1378_;
goto v___jp_1362_;
}
v___jp_1362_:
{
uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v_fold_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1364_ = 32ULL;
v___x_1365_ = lean_uint64_shift_right(v___y_1363_, v___x_1364_);
v_fold_1366_ = lean_uint64_xor(v___y_1363_, v___x_1365_);
v___x_1367_ = 16ULL;
v___x_1368_ = lean_uint64_shift_right(v_fold_1366_, v___x_1367_);
v___x_1369_ = lean_uint64_xor(v_fold_1366_, v___x_1368_);
v___x_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = lean_usize_of_nat(v___x_1361_);
v___x_1372_ = ((size_t)1ULL);
v___x_1373_ = lean_usize_sub(v___x_1371_, v___x_1372_);
v___x_1374_ = lean_usize_land(v___x_1370_, v___x_1373_);
v___x_1375_ = lean_array_uget_borrowed(v_buckets_1360_, v___x_1374_);
v___x_1376_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1359_, v___x_1375_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_m_1379_);
return v_res_1381_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1385_, uint8_t v_isMeta_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v_env_1395_; lean_object* v___y_1397_; lean_object* v___x_1410_; 
v___x_1390_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0);
v___x_1391_ = lean_st_ref_get(v___y_1388_);
v_env_1395_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_env_1395_);
lean_dec(v___x_1391_);
v___x_1410_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1395_, v_declName_1385_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_dec_ref(v_env_1395_);
lean_dec(v_declName_1385_);
goto v___jp_1392_;
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1412_; lean_object* v_modules_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_val_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = l_Lean_Environment_header(v_env_1395_);
v_modules_1413_ = lean_ctor_get(v___x_1412_, 3);
lean_inc_ref(v_modules_1413_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = lean_array_get_size(v_modules_1413_);
v___x_1415_ = lean_nat_dec_lt(v_val_1411_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_dec_ref(v_modules_1413_);
lean_dec(v_val_1411_);
lean_dec_ref(v_env_1395_);
lean_dec(v_declName_1385_);
goto v___jp_1392_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___y_1419_; 
v___x_1416_ = lean_array_fget(v_modules_1413_, v_val_1411_);
lean_dec(v_val_1411_);
lean_dec_ref(v_modules_1413_);
v___x_1417_ = lean_st_ref_get(v___y_1388_);
if (v_isMeta_1386_ == 0)
{
lean_dec(v___x_1417_);
v___y_1419_ = v_isMeta_1386_;
goto v___jp_1418_;
}
else
{
lean_object* v_env_1430_; uint8_t v___x_1431_; 
v_env_1430_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_env_1430_);
lean_dec(v___x_1417_);
lean_inc(v_declName_1385_);
v___x_1431_ = l_Lean_isMarkedMeta(v_env_1430_, v_declName_1385_);
if (v___x_1431_ == 0)
{
v___y_1419_ = v_isMeta_1386_;
goto v___jp_1418_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = 0;
v___y_1419_ = v___x_1432_;
goto v___jp_1418_;
}
}
v___jp_1418_:
{
lean_object* v_toImport_1420_; lean_object* v_module_1421_; lean_object* v___x_1422_; 
v_toImport_1420_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_toImport_1420_);
lean_dec(v___x_1416_);
v_module_1421_ = lean_ctor_get(v_toImport_1420_, 0);
lean_inc(v_module_1421_);
lean_dec_ref(v_toImport_1420_);
lean_inc(v_declName_1385_);
v___x_1422_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1421_, v___y_1419_, v_declName_1385_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref_known(v___x_1422_, 1);
v___x_1423_ = l_Lean_indirectModUseExt;
v___x_1424_ = lean_box(1);
v___x_1425_ = lean_box(0);
lean_inc_ref(v_env_1395_);
v___x_1426_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1390_, v___x_1423_, v_env_1395_, v___x_1424_, v___x_1425_);
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1426_, v_declName_1385_);
lean_dec(v___x_1426_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___y_1397_ = v___x_1428_;
goto v___jp_1396_;
}
else
{
lean_object* v_val_1429_; 
v_val_1429_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1427_, 1);
v___y_1397_ = v_val_1429_;
goto v___jp_1396_;
}
}
else
{
lean_dec_ref(v_env_1395_);
lean_dec(v_declName_1385_);
return v___x_1422_;
}
}
}
}
v___jp_1392_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
v___jp_1396_:
{
lean_object* v___x_1398_; size_t v_sz_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_box(0);
v_sz_1399_ = lean_array_size(v___y_1397_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1395_, v_declName_1385_, v___y_1397_, v_sz_1399_, v___x_1400_, v___x_1398_, v___y_1387_, v___y_1388_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v_env_1395_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1409_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1398_);
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1398_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1433_, lean_object* v_isMeta_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v_isMeta_boxed_1438_; lean_object* v_res_1439_; 
v_isMeta_boxed_1438_ = lean_unbox(v_isMeta_1434_);
v_res_1439_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1433_, v_isMeta_boxed_1438_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
if (lean_obj_tag(v_as_x27_1440_) == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_b_1441_);
return v___x_1445_;
}
else
{
lean_object* v_head_1446_; lean_object* v_tail_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
v_head_1446_ = lean_ctor_get(v_as_x27_1440_, 0);
v_tail_1447_ = lean_ctor_get(v_as_x27_1440_, 1);
v___x_1448_ = lean_box(0);
v___x_1449_ = 1;
lean_inc(v_head_1446_);
v___x_1450_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1446_, v___x_1449_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref_known(v___x_1450_, 1);
v_as_x27_1440_ = v_tail_1447_;
v_b_1441_ = v___x_1448_;
goto _start;
}
else
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1452_, v_b_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_as_x27_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1458_, lean_object* v_opts_1459_, lean_object* v_currNamespace_1460_, lean_object* v_openDecls_1461_, lean_object* v_n_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = l_Lean_ResolveName_resolveGlobalName(v_env_1458_, v_opts_1459_, v_currNamespace_1460_, v_openDecls_1461_, v_n_1462_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___y_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1467_, lean_object* v_opts_1468_, lean_object* v_currNamespace_1469_, lean_object* v_openDecls_1470_, lean_object* v_n_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1467_, v_opts_1468_, v_currNamespace_1469_, v_openDecls_1470_, v_n_1471_, v___y_1472_, v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v_opts_1468_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Elab_Command_getRef___redArg(v___y_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v_fileName_1482_; lean_object* v_fileMap_1483_; lean_object* v_currRecDepth_1484_; lean_object* v_cmdPos_1485_; lean_object* v_macroStack_1486_; lean_object* v_quotContext_x3f_1487_; lean_object* v_currMacroScope_1488_; lean_object* v_snap_x3f_1489_; lean_object* v_cancelTk_x3f_1490_; uint8_t v_suppressElabErrors_1491_; lean_object* v_ref_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v_fileName_1482_ = lean_ctor_get(v___y_1477_, 0);
v_fileMap_1483_ = lean_ctor_get(v___y_1477_, 1);
v_currRecDepth_1484_ = lean_ctor_get(v___y_1477_, 2);
v_cmdPos_1485_ = lean_ctor_get(v___y_1477_, 3);
v_macroStack_1486_ = lean_ctor_get(v___y_1477_, 4);
v_quotContext_x3f_1487_ = lean_ctor_get(v___y_1477_, 5);
v_currMacroScope_1488_ = lean_ctor_get(v___y_1477_, 6);
v_snap_x3f_1489_ = lean_ctor_get(v___y_1477_, 8);
v_cancelTk_x3f_1490_ = lean_ctor_get(v___y_1477_, 9);
v_suppressElabErrors_1491_ = lean_ctor_get_uint8(v___y_1477_, sizeof(void*)*10);
v_ref_1492_ = l_Lean_replaceRef(v_ref_1475_, v_a_1481_);
lean_dec(v_a_1481_);
lean_inc(v_cancelTk_x3f_1490_);
lean_inc(v_snap_x3f_1489_);
lean_inc(v_currMacroScope_1488_);
lean_inc(v_quotContext_x3f_1487_);
lean_inc(v_macroStack_1486_);
lean_inc(v_cmdPos_1485_);
lean_inc(v_currRecDepth_1484_);
lean_inc_ref(v_fileMap_1483_);
lean_inc_ref(v_fileName_1482_);
v___x_1493_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1493_, 0, v_fileName_1482_);
lean_ctor_set(v___x_1493_, 1, v_fileMap_1483_);
lean_ctor_set(v___x_1493_, 2, v_currRecDepth_1484_);
lean_ctor_set(v___x_1493_, 3, v_cmdPos_1485_);
lean_ctor_set(v___x_1493_, 4, v_macroStack_1486_);
lean_ctor_set(v___x_1493_, 5, v_quotContext_x3f_1487_);
lean_ctor_set(v___x_1493_, 6, v_currMacroScope_1488_);
lean_ctor_set(v___x_1493_, 7, v_ref_1492_);
lean_ctor_set(v___x_1493_, 8, v_snap_x3f_1489_);
lean_ctor_set(v___x_1493_, 9, v_cancelTk_x3f_1490_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*10, v_suppressElabErrors_1491_);
v___x_1494_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1476_, v___x_1493_, v___y_1478_);
lean_dec_ref_known(v___x_1493_, 10);
return v___x_1494_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v_msg_1476_);
v_a_1495_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1480_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1480_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1503_, v_msg_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_ref_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1509_, lean_object* v_currNamespace_1510_, lean_object* v_openDecls_1511_, lean_object* v_n_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = l_Lean_ResolveName_resolveNamespace(v_env_1509_, v_currNamespace_1510_, v_openDecls_1511_, v_n_1512_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___y_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1517_, lean_object* v_currNamespace_1518_, lean_object* v_openDecls_1519_, lean_object* v_n_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1517_, v_currNamespace_1518_, v_openDecls_1519_, v_n_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_currNamespace_1524_);
lean_ctor_set(v___x_1527_, 1, v___y_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1528_, v___y_1529_, v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1532_, lean_object* v___y_1533_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_a_1534_);
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1534_);
lean_ctor_set(v___x_1535_, 1, v___y_1533_);
return v___x_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_a_1536_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1536_);
lean_ctor_set(v___x_1537_, 1, v___y_1533_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1538_, v___y_1539_);
lean_dec_ref(v_x_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1541_, lean_object* v_stx_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1541_, v_stx_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
if (lean_obj_tag(v_a_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_a_1547_ = lean_ctor_get(v___x_1545_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1556_);
v___x_1549_ = v___x_1545_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_box(0);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_a_1547_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1585_; 
v_val_1557_ = lean_ctor_get(v_a_1546_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_a_1546_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1559_ = v_a_1546_;
v_isShared_1560_ = v_isSharedCheck_1585_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v_a_1546_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1585_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_snd_1561_; 
v_snd_1561_ = lean_ctor_get(v_val_1557_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_val_1557_);
if (lean_obj_tag(v_snd_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1559_);
v_a_1562_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1545_, 2);
v_a_1563_ = lean_ctor_get(v_snd_1561_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_snd_1561_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1565_ = v_snd_1561_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v_snd_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1568_, v_a_1562_);
lean_dec_ref(v___x_1568_);
return v___x_1569_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1584_; 
v_a_1572_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1545_, 2);
v_a_1573_ = lean_ctor_get(v_snd_1561_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_snd_1561_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1575_ = v_snd_1561_;
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v_snd_1561_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v_a_1573_);
v___x_1578_ = v___x_1559_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1580_, v_a_1572_);
lean_dec_ref(v___x_1580_);
return v___x_1581_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1586_ = lean_ctor_get(v___x_1545_, 0);
v_a_1587_ = lean_ctor_get(v___x_1545_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1545_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1545_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1595_, lean_object* v_stx_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1595_, v_stx_1596_, v___y_1597_, v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1599_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
if (lean_obj_tag(v_as_1608_) == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
else
{
lean_object* v_head_1614_; lean_object* v_tail_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_scopes_1622_; lean_object* v___x_1623_; lean_object* v_opts_1624_; uint8_t v_hasTrace_1625_; 
v_head_1614_ = lean_ctor_get(v_as_1608_, 0);
lean_inc(v_head_1614_);
v_tail_1615_ = lean_ctor_get(v_as_1608_, 1);
lean_inc(v_tail_1615_);
lean_dec_ref_known(v_as_1608_, 2);
v_fst_1616_ = lean_ctor_get(v_head_1614_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v_head_1614_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_head_1614_);
v___x_1618_ = l_Lean_inheritedTraceOptions;
v___x_1619_ = lean_st_ref_get(v___x_1618_);
v___x_1620_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1621_ = lean_st_ref_get(v___y_1610_);
v_scopes_1622_ = lean_ctor_get(v___x_1621_, 2);
lean_inc(v_scopes_1622_);
lean_dec(v___x_1621_);
v___x_1623_ = l_List_head_x21___redArg(v___x_1620_, v_scopes_1622_);
lean_dec(v_scopes_1622_);
v_opts_1624_ = lean_ctor_get(v___x_1623_, 1);
lean_inc_ref(v_opts_1624_);
lean_dec(v___x_1623_);
v_hasTrace_1625_ = lean_ctor_get_uint8(v_opts_1624_, sizeof(void*)*1);
if (v_hasTrace_1625_ == 0)
{
lean_dec_ref(v_opts_1624_);
lean_dec(v___x_1619_);
lean_dec(v_snd_1617_);
lean_dec(v_fst_1616_);
v_as_1608_ = v_tail_1615_;
goto _start;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
lean_inc(v_fst_1616_);
v___x_1628_ = l_Lean_Name_append(v___x_1627_, v_fst_1616_);
v___x_1629_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1619_, v_opts_1624_, v___x_1628_);
lean_dec(v___x_1628_);
lean_dec_ref(v_opts_1624_);
lean_dec(v___x_1619_);
if (v___x_1629_ == 0)
{
lean_dec(v_snd_1617_);
lean_dec(v_fst_1616_);
v_as_1608_ = v_tail_1615_;
goto _start;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_snd_1617_);
v___x_1632_ = l_Lean_MessageData_ofFormat(v___x_1631_);
v___x_1633_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1616_, v___x_1632_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_dec_ref_known(v___x_1633_, 1);
v_as_1608_ = v_tail_1615_;
goto _start;
}
else
{
lean_dec(v_tail_1615_);
return v___x_1633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v_env_1646_; lean_object* v___f_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_scopes_1651_; lean_object* v___x_1652_; lean_object* v_opts_1653_; lean_object* v___x_1654_; 
v___x_1645_ = lean_st_ref_get(v___y_1643_);
v_env_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc_ref_n(v_env_1646_, 3);
lean_dec(v___x_1645_);
v___f_1647_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1647_, 0, v_env_1646_);
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1648_, 0, v_env_1646_);
v___x_1649_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1650_ = lean_st_ref_get(v___y_1643_);
v_scopes_1651_ = lean_ctor_get(v___x_1650_, 2);
lean_inc(v_scopes_1651_);
lean_dec(v___x_1650_);
v___x_1652_ = l_List_head_x21___redArg(v___x_1649_, v_scopes_1651_);
lean_dec(v_scopes_1651_);
v_opts_1653_ = lean_ctor_get(v___x_1652_, 1);
lean_inc_ref(v_opts_1653_);
lean_dec(v___x_1652_);
v___x_1654_ = l_Lean_Elab_Command_getScope___redArg(v___y_1643_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v_currNamespace_1656_; lean_object* v___f_1657_; lean_object* v___x_1658_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v_currNamespace_1656_ = lean_ctor_get(v_a_1655_, 2);
lean_inc_n(v_currNamespace_1656_, 2);
lean_dec(v_a_1655_);
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1657_, 0, v_currNamespace_1656_);
v___x_1658_ = l_Lean_Elab_Command_getScope___redArg(v___y_1643_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_openDecls_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v_methods_1663_; lean_object* v___x_1664_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_openDecls_1660_ = lean_ctor_get(v_a_1659_, 3);
lean_inc_n(v_openDecls_1660_, 2);
lean_dec(v_a_1659_);
lean_inc(v_currNamespace_1656_);
lean_inc_ref(v_env_1646_);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1661_, 0, v_env_1646_);
lean_closure_set(v___f_1661_, 1, v_currNamespace_1656_);
lean_closure_set(v___f_1661_, 2, v_openDecls_1660_);
v___f_1662_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1662_, 0, v_env_1646_);
lean_closure_set(v___f_1662_, 1, v_opts_1653_);
lean_closure_set(v___f_1662_, 2, v_currNamespace_1656_);
lean_closure_set(v___f_1662_, 3, v_openDecls_1660_);
v_methods_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1663_, 0, v___f_1648_);
lean_ctor_set(v_methods_1663_, 1, v___f_1657_);
lean_ctor_set(v_methods_1663_, 2, v___f_1647_);
lean_ctor_set(v_methods_1663_, 3, v___f_1661_);
lean_ctor_set(v_methods_1663_, 4, v___f_1662_);
v___x_1664_ = l_Lean_Elab_Command_getRef___redArg(v___y_1642_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1642_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v_currRecDepth_1668_; lean_object* v_quotContext_x3f_1669_; lean_object* v_a_1671_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v_currRecDepth_1668_ = lean_ctor_get(v___y_1642_, 2);
v_quotContext_x3f_1669_ = lean_ctor_get(v___y_1642_, 5);
if (lean_obj_tag(v_quotContext_x3f_1669_) == 0)
{
lean_object* v___x_1745_; lean_object* v_a_1746_; 
v___x_1745_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1643_);
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v___x_1745_);
v_a_1671_ = v_a_1746_;
goto v___jp_1670_;
}
else
{
lean_object* v_val_1747_; 
v_val_1747_ = lean_ctor_get(v_quotContext_x3f_1669_, 0);
lean_inc(v_val_1747_);
v_a_1671_ = v_val_1747_;
goto v___jp_1670_;
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v_maxRecDepth_1673_; lean_object* v___x_1674_; lean_object* v_nextMacroScope_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1672_ = lean_st_ref_get(v___y_1643_);
v_maxRecDepth_1673_ = lean_ctor_get(v___x_1672_, 5);
lean_inc(v_maxRecDepth_1673_);
lean_dec(v___x_1672_);
v___x_1674_ = lean_st_ref_get(v___y_1643_);
v_nextMacroScope_1675_ = lean_ctor_get(v___x_1674_, 4);
lean_inc(v_nextMacroScope_1675_);
lean_dec(v___x_1674_);
lean_inc(v_currRecDepth_1668_);
v___x_1676_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1676_, 0, v_methods_1663_);
lean_ctor_set(v___x_1676_, 1, v_a_1671_);
lean_ctor_set(v___x_1676_, 2, v_a_1667_);
lean_ctor_set(v___x_1676_, 3, v_currRecDepth_1668_);
lean_ctor_set(v___x_1676_, 4, v_maxRecDepth_1673_);
lean_ctor_set(v___x_1676_, 5, v_a_1665_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1678_, 0, v_nextMacroScope_1675_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
lean_ctor_set(v___x_1678_, 2, v___x_1677_);
v___x_1679_ = lean_apply_2(v_x_1641_, v___x_1676_, v___x_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v_a_1681_; lean_object* v_macroScope_1682_; lean_object* v_traceMsgs_1683_; lean_object* v_expandedMacroDecls_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 1);
lean_inc(v_a_1680_);
v_a_1681_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1679_, 2);
v_macroScope_1682_ = lean_ctor_get(v_a_1680_, 0);
lean_inc(v_macroScope_1682_);
v_traceMsgs_1683_ = lean_ctor_get(v_a_1680_, 1);
lean_inc(v_traceMsgs_1683_);
v_expandedMacroDecls_1684_ = lean_ctor_get(v_a_1680_, 2);
lean_inc(v_expandedMacroDecls_1684_);
lean_dec(v_a_1680_);
v___x_1685_ = lean_box(0);
v___x_1686_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1684_, v___x_1685_, v___y_1642_, v___y_1643_);
lean_dec(v_expandedMacroDecls_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; lean_object* v_env_1688_; lean_object* v_messages_1689_; lean_object* v_scopes_1690_; lean_object* v_usedQuotCtxts_1691_; lean_object* v_maxRecDepth_1692_; lean_object* v_ngen_1693_; lean_object* v_auxDeclNGen_1694_; lean_object* v_infoState_1695_; lean_object* v_traceState_1696_; lean_object* v_snapshotTasks_1697_; lean_object* v_prevLinterStates_1698_; lean_object* v_codeQualityEntryTasks_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref_known(v___x_1686_, 1);
v___x_1687_ = lean_st_ref_take(v___y_1643_);
v_env_1688_ = lean_ctor_get(v___x_1687_, 0);
v_messages_1689_ = lean_ctor_get(v___x_1687_, 1);
v_scopes_1690_ = lean_ctor_get(v___x_1687_, 2);
v_usedQuotCtxts_1691_ = lean_ctor_get(v___x_1687_, 3);
v_maxRecDepth_1692_ = lean_ctor_get(v___x_1687_, 5);
v_ngen_1693_ = lean_ctor_get(v___x_1687_, 6);
v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1687_, 7);
v_infoState_1695_ = lean_ctor_get(v___x_1687_, 8);
v_traceState_1696_ = lean_ctor_get(v___x_1687_, 9);
v_snapshotTasks_1697_ = lean_ctor_get(v___x_1687_, 10);
v_prevLinterStates_1698_ = lean_ctor_get(v___x_1687_, 11);
v_codeQualityEntryTasks_1699_ = lean_ctor_get(v___x_1687_, 12);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1687_, 4);
lean_dec(v_unused_1726_);
v___x_1701_ = v___x_1687_;
v_isShared_1702_ = v_isSharedCheck_1725_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1699_);
lean_inc(v_prevLinterStates_1698_);
lean_inc(v_snapshotTasks_1697_);
lean_inc(v_traceState_1696_);
lean_inc(v_infoState_1695_);
lean_inc(v_auxDeclNGen_1694_);
lean_inc(v_ngen_1693_);
lean_inc(v_maxRecDepth_1692_);
lean_inc(v_usedQuotCtxts_1691_);
lean_inc(v_scopes_1690_);
lean_inc(v_messages_1689_);
lean_inc(v_env_1688_);
lean_dec(v___x_1687_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1725_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 4, v_macroScope_1682_);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_env_1688_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_messages_1689_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_scopes_1690_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_usedQuotCtxts_1691_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_macroScope_1682_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_maxRecDepth_1692_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_ngen_1693_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_auxDeclNGen_1694_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_infoState_1695_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_traceState_1696_);
lean_ctor_set(v_reuseFailAlloc_1724_, 10, v_snapshotTasks_1697_);
lean_ctor_set(v_reuseFailAlloc_1724_, 11, v_prevLinterStates_1698_);
lean_ctor_set(v_reuseFailAlloc_1724_, 12, v_codeQualityEntryTasks_1699_);
v___x_1704_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_st_ref_put(v___y_1643_, v___x_1704_);
v___x_1706_ = l_List_reverse___redArg(v_traceMsgs_1683_);
v___x_1707_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1706_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v___x_1707_, 0);
lean_dec(v_unused_1715_);
v___x_1709_ = v___x_1707_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v___x_1707_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_a_1681_);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1681_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1681_);
v_a_1716_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1707_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1707_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_traceMsgs_1683_);
lean_dec(v_macroScope_1682_);
lean_dec(v_a_1681_);
v_a_1727_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1686_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1686_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_a_1735_; 
v_a_1735_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1679_, 2);
if (lean_obj_tag(v_a_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v_a_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_a_1736_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_a_1736_);
v_a_1737_ = lean_ctor_get(v_a_1735_, 1);
lean_inc_ref(v_a_1737_);
lean_dec_ref_known(v_a_1735_, 2);
v___x_1738_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1739_ = lean_string_dec_eq(v_a_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_a_1737_);
v___x_1741_ = l_Lean_MessageData_ofFormat(v___x_1740_);
v___x_1742_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1736_, v___x_1741_, v___y_1642_, v___y_1643_);
lean_dec(v_a_1736_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; 
lean_dec_ref(v_a_1737_);
v___x_1743_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1736_);
return v___x_1743_;
}
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1665_);
lean_dec_ref_known(v_methods_1663_, 5);
lean_dec_ref(v_x_1641_);
v_a_1748_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1666_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1666_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref_known(v_methods_1663_, 5);
lean_dec_ref(v_x_1641_);
v_a_1756_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1664_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1664_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v___f_1657_);
lean_dec(v_currNamespace_1656_);
lean_dec_ref(v_opts_1653_);
lean_dec_ref(v___f_1648_);
lean_dec_ref(v___f_1647_);
lean_dec_ref(v_env_1646_);
lean_dec_ref(v_x_1641_);
v_a_1764_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1658_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1658_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v_opts_1653_);
lean_dec_ref(v___f_1648_);
lean_dec_ref(v___f_1647_);
lean_dec_ref(v_env_1646_);
lean_dec_ref(v_x_1641_);
v_a_1772_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1654_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1654_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1784_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1799_ = l_String_toRawSubstring_x27(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1822_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1823_ = lean_unsigned_to_nat(14u);
v___x_1824_ = lean_unsigned_to_nat(22u);
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1826_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1827_ = l_mkPanicMessageWithDecl(v___x_1826_, v___x_1825_, v___x_1824_, v___x_1823_, v___x_1822_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1844_ = l_String_toRawSubstring_x27(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1857_ = l_Lean_mkAtom(v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1860_ = l_Lean_mkAtom(v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1861_, lean_object* v_id_1862_, lean_object* v_stx_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_pat_1868_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1863_);
v___x_1872_ = l_Lean_Syntax_isOfKind(v_stx_1863_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1863_);
v___x_1874_ = l_Lean_Syntax_isOfKind(v_stx_1863_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v_a_1881_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_a_1915_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v_a_1949_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v_a_1985_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v_a_2019_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v_a_2053_; uint8_t v___x_2084_; 
v___x_1875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1863_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v_stx_1863_, v___x_1875_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1863_);
v___x_2086_ = l_Lean_Syntax_isOfKind(v_stx_1863_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1863_);
v___x_2088_ = l_Lean_Syntax_isOfKind(v_stx_1863_, v___x_2087_);
if (v___x_2088_ == 0)
{
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_SourceInfo_fromRef(v_a_2090_, v___x_2088_);
lean_dec(v_a_2090_);
v___x_2092_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v_a_2095_; lean_object* v_quotContext_x3f_2126_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v_quotContext_x3f_2126_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2126_) == 0)
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v_a_2095_ = v_a_2128_;
goto v___jp_2094_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_2093_);
lean_dec(v___x_2091_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2129_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2127_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_val_2137_; 
v_val_2137_ = lean_ctor_get(v_quotContext_x3f_2126_, 0);
lean_inc(v_val_2137_);
v_a_2095_ = v_val_2137_;
goto v___jp_2094_;
}
v___jp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2096_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2097_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2098_ = l_Lean_addMacroScope(v_a_2095_, v___x_2097_, v_a_2093_);
v___x_2099_ = lean_box(0);
lean_inc_n(v___x_2091_, 4);
v___x_2100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2091_);
lean_ctor_set(v___x_2100_, 1, v___x_2096_);
lean_ctor_set(v___x_2100_, 2, v___x_2098_);
lean_ctor_set(v___x_2100_, 3, v___x_2099_);
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2091_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2104_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2103_, v_stx_1863_);
v___x_2105_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2091_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = l_Lean_Syntax_node4(v___x_2091_, v___x_1875_, v___x_2100_, v___x_2102_, v___x_2104_, v___x_2106_);
v___x_2108_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2117_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2107_);
lean_ctor_set(v___x_2113_, 1, v_a_2109_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2113_);
v___x_2115_ = v___x_2111_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v___x_2107_);
v_a_2118_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2108_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2108_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v___x_2091_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2138_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2092_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2092_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2146_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2089_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2089_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_val_2154_; lean_object* v___x_2155_; 
lean_dec(v_id_1862_);
v_val_2154_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2155_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2154_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
v_pat_1868_ = v_a_2156_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_stx_1863_);
v_a_2157_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2155_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2165_);
lean_inc(v___x_2166_);
v___x_2167_ = l_Lean_Syntax_matchesNull(v___x_2166_, v___x_2165_);
if (v___x_2167_ == 0)
{
lean_dec(v___x_2166_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = l_Lean_SourceInfo_fromRef(v_a_2169_, v___x_2167_);
lean_dec(v_a_2169_);
v___x_2171_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v_a_2174_; lean_object* v_quotContext_x3f_2205_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v_quotContext_x3f_2205_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2205_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v_a_2174_ = v_a_2207_;
goto v___jp_2173_;
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_a_2172_);
lean_dec(v___x_2170_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2208_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2206_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2206_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_val_2216_; 
v_val_2216_ = lean_ctor_get(v_quotContext_x3f_2205_, 0);
lean_inc(v_val_2216_);
v_a_2174_ = v_val_2216_;
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2175_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2177_ = l_Lean_addMacroScope(v_a_2174_, v___x_2176_, v_a_2172_);
v___x_2178_ = lean_box(0);
lean_inc_n(v___x_2170_, 4);
v___x_2179_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2170_);
lean_ctor_set(v___x_2179_, 1, v___x_2175_);
lean_ctor_set(v___x_2179_, 2, v___x_2177_);
lean_ctor_set(v___x_2179_, 3, v___x_2178_);
v___x_2180_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2170_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2183_ = l_Lean_Syntax_node1(v___x_2170_, v___x_2182_, v_stx_1863_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2170_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_Syntax_node4(v___x_2170_, v___x_1875_, v___x_2179_, v___x_2181_, v___x_2183_, v___x_2185_);
v___x_2187_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2196_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2186_);
lean_ctor_set(v___x_2192_, 1, v_a_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v___x_2186_);
v_a_2197_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2187_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2187_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v___x_2170_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2217_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2171_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2171_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2225_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2168_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2168_);
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
lean_object* v_val_2233_; lean_object* v___x_2234_; 
lean_dec(v_id_1862_);
v_val_2233_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2234_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2233_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v_pat_1868_ = v_a_2235_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_stx_1863_);
v_a_2236_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v_stx_2245_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2275_; lean_object* v___y_2276_; 
v___x_2244_ = lean_unsigned_to_nat(0u);
v_stx_2245_ = l_Lean_Syntax_getArg(v___x_2166_, v___x_2244_);
lean_dec(v___x_2166_);
v___x_2263_ = lean_unsigned_to_nat(2u);
v___x_2264_ = lean_unsigned_to_nat(3u);
v___x_2265_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2264_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2265_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v___x_2265_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_dec(v___x_2265_);
lean_dec(v_stx_2245_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = l_Lean_SourceInfo_fromRef(v_a_2426_, v___x_2086_);
lean_dec(v_a_2426_);
v___x_2428_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v_a_2431_; lean_object* v_quotContext_x3f_2462_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v_quotContext_x3f_2462_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2462_) == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v_a_2431_ = v_a_2464_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2429_);
lean_dec(v___x_2427_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2465_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2463_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_val_2473_; 
v_val_2473_ = lean_ctor_get(v_quotContext_x3f_2462_, 0);
lean_inc(v_val_2473_);
v_a_2431_ = v_val_2473_;
goto v___jp_2430_;
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2432_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2433_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2434_ = l_Lean_addMacroScope(v_a_2431_, v___x_2433_, v_a_2429_);
v___x_2435_ = lean_box(0);
lean_inc_n(v___x_2427_, 4);
v___x_2436_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2427_);
lean_ctor_set(v___x_2436_, 1, v___x_2432_);
lean_ctor_set(v___x_2436_, 2, v___x_2434_);
lean_ctor_set(v___x_2436_, 3, v___x_2435_);
v___x_2437_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2427_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2440_ = l_Lean_Syntax_node1(v___x_2427_, v___x_2439_, v_stx_1863_);
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2427_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_Syntax_node4(v___x_2427_, v___x_1875_, v___x_2436_, v___x_2438_, v___x_2440_, v___x_2442_);
v___x_2444_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2453_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2453_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2453_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2443_);
lean_ctor_set(v___x_2449_, 1, v_a_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2449_);
v___x_2451_ = v___x_2447_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v___x_2443_);
v_a_2454_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2444_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2444_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___x_2427_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2474_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2428_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2428_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2482_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2425_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2425_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_val_2490_; lean_object* v___x_2491_; 
lean_dec(v_id_1862_);
v_val_2490_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2491_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2490_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v_pat_1868_ = v_a_2492_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_stx_1863_);
v_a_2493_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
goto v___jp_2326_;
}
}
else
{
goto v___jp_2326_;
}
v___jp_2246_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2252_ = lean_string_append(v___y_2250_, v___x_2251_);
lean_inc(v___y_2247_);
v___x_2253_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2247_, v_stx_2245_, v_id_1862_, v___x_2252_, v___y_2249_, v___y_2248_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v_pat_1868_ = v_a_2254_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_stx_1863_);
v_a_2255_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2253_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2253_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
v___jp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2270_ = l_Lean_Syntax_isStrLit_x3f(v___x_2265_);
lean_dec(v___x_2265_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2272_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2271_);
v___y_2247_ = v___x_2269_;
v___y_2248_ = v___y_2268_;
v___y_2249_ = v___y_2267_;
v___y_2250_ = v___x_2272_;
goto v___jp_2246_;
}
else
{
lean_object* v_val_2273_; 
v_val_2273_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v___x_2270_, 1);
v___y_2247_ = v___x_2269_;
v___y_2248_ = v___y_2268_;
v___y_2249_ = v___y_2267_;
v___y_2250_ = v_val_2273_;
goto v___jp_2246_;
}
}
v___jp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2277_ = lean_unsigned_to_nat(5u);
v___x_2278_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2277_);
v___x_2279_ = l_Lean_Syntax_isNone(v___x_2278_);
if (v___x_2279_ == 0)
{
uint8_t v___x_2280_; 
v___x_2280_ = l_Lean_Syntax_matchesNull(v___x_2278_, v___x_2263_);
if (v___x_2280_ == 0)
{
lean_dec(v___x_2265_);
lean_dec(v_stx_2245_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Elab_Command_getRef___redArg(v___y_2275_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = l_Lean_SourceInfo_fromRef(v_a_2282_, v___x_2280_);
lean_dec(v_a_2282_);
v___x_2284_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2275_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_quotContext_x3f_2285_; 
v_quotContext_x3f_2285_ = lean_ctor_get(v___y_2275_, 5);
if (lean_obj_tag(v_quotContext_x3f_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2287_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2276_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___y_1877_ = v_a_2286_;
v___y_1878_ = v___x_2283_;
v___y_1879_ = v___y_2276_;
v___y_1880_ = v___y_2275_;
v_a_1881_ = v_a_2288_;
goto v___jp_1876_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_a_2286_);
lean_dec(v___x_2283_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2289_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2287_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2287_);
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
lean_object* v_a_2297_; lean_object* v_val_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2284_, 1);
v_val_2298_ = lean_ctor_get(v_quotContext_x3f_2285_, 0);
lean_inc(v_val_2298_);
v___y_1877_ = v_a_2297_;
v___y_1878_ = v___x_2283_;
v___y_1879_ = v___y_2276_;
v___y_1880_ = v___y_2275_;
v_a_1881_ = v_val_2298_;
goto v___jp_1876_;
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v___x_2283_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2299_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2284_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2284_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2307_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2281_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2281_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_val_2315_; lean_object* v___x_2316_; 
lean_dec(v_id_1862_);
v_val_2315_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2315_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2316_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2315_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v_pat_1868_ = v_a_2317_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_stx_1863_);
v_a_2318_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2316_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2316_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1861_);
v___y_2267_ = v___y_2275_;
v___y_2268_ = v___y_2276_;
goto v___jp_2266_;
}
}
else
{
lean_dec(v___x_2278_);
lean_dec(v_id_x3f_1861_);
v___y_2267_ = v___y_2275_;
v___y_2268_ = v___y_2276_;
goto v___jp_2266_;
}
}
v___jp_2326_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(4u);
v___x_2328_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2327_);
v___x_2329_ = l_Lean_Syntax_isNone(v___x_2328_);
if (v___x_2329_ == 0)
{
uint8_t v___x_2330_; 
lean_inc(v___x_2328_);
v___x_2330_ = l_Lean_Syntax_matchesNull(v___x_2328_, v___x_2263_);
if (v___x_2330_ == 0)
{
lean_dec(v___x_2328_);
lean_dec(v___x_2265_);
lean_dec(v_stx_2245_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = l_Lean_SourceInfo_fromRef(v_a_2332_, v___x_2330_);
lean_dec(v_a_2332_);
v___x_2334_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_quotContext_x3f_2335_; 
v_quotContext_x3f_2335_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2337_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___y_1913_ = v_a_2336_;
v___y_1914_ = v___x_2333_;
v_a_1915_ = v_a_2338_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_a_2336_);
lean_dec(v___x_2333_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
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
else
{
lean_object* v_a_2347_; lean_object* v_val_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2334_, 1);
v_val_2348_ = lean_ctor_get(v_quotContext_x3f_2335_, 0);
lean_inc(v_val_2348_);
v___y_1913_ = v_a_2347_;
v___y_1914_ = v___x_2333_;
v_a_1915_ = v_val_2348_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v___x_2333_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2349_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2334_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2334_);
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
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2357_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2331_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2331_);
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
lean_object* v_val_2365_; lean_object* v___x_2366_; 
lean_dec(v_id_1862_);
v_val_2365_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2365_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2366_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2365_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v_pat_1868_ = v_a_2367_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_stx_1863_);
v_a_2368_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2366_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2366_);
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
}
else
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = l_Lean_Syntax_getArg(v___x_2328_, v___x_2165_);
lean_dec(v___x_2328_);
v___x_2377_ = l_Lean_Syntax_matchesNull(v___x_2376_, v___x_2165_);
if (v___x_2377_ == 0)
{
lean_dec(v___x_2265_);
lean_dec(v_stx_2245_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = l_Lean_SourceInfo_fromRef(v_a_2379_, v___x_2377_);
lean_dec(v_a_2379_);
v___x_2381_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_quotContext_x3f_2382_; 
v_quotContext_x3f_2382_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2383_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2384_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___y_1947_ = v___x_2380_;
v___y_1948_ = v_a_2383_;
v_a_1949_ = v_a_2385_;
goto v___jp_1946_;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_a_2383_);
lean_dec(v___x_2380_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2386_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2384_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2384_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v_val_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2381_, 1);
v_val_2395_ = lean_ctor_get(v_quotContext_x3f_2382_, 0);
lean_inc(v_val_2395_);
v___y_1947_ = v___x_2380_;
v___y_1948_ = v_a_2394_;
v_a_1949_ = v_val_2395_;
goto v___jp_1946_;
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v___x_2380_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2396_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2381_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2381_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2404_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2378_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2378_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_val_2412_; lean_object* v___x_2413_; 
lean_dec(v_id_1862_);
v_val_2412_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2413_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2412_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v_pat_1868_ = v_a_2414_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_stx_1863_);
v_a_2415_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2413_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2413_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
else
{
v___y_2275_ = v_a_1864_;
v___y_2276_ = v_a_1865_;
goto v___jp_2274_;
}
}
}
else
{
lean_dec(v___x_2328_);
v___y_2275_ = v_a_1864_;
v___y_2276_ = v_a_1865_;
goto v___jp_2274_;
}
}
}
}
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2501_ = lean_unsigned_to_nat(1u);
v___x_2502_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2501_);
lean_inc(v___x_2502_);
v___x_2503_ = l_Lean_Syntax_matchesNull(v___x_2502_, v___x_2501_);
if (v___x_2503_ == 0)
{
lean_dec(v___x_2502_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l_Lean_SourceInfo_fromRef(v_a_2505_, v___x_2503_);
lean_dec(v_a_2505_);
v___x_2507_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v_a_2510_; lean_object* v_quotContext_x3f_2541_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v_quotContext_x3f_2541_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2541_) == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v_a_2510_ = v_a_2543_;
goto v___jp_2509_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_a_2508_);
lean_dec(v___x_2506_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2544_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2542_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_val_2552_; 
v_val_2552_ = lean_ctor_get(v_quotContext_x3f_2541_, 0);
lean_inc(v_val_2552_);
v_a_2510_ = v_val_2552_;
goto v___jp_2509_;
}
v___jp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2511_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2513_ = l_Lean_addMacroScope(v_a_2510_, v___x_2512_, v_a_2508_);
v___x_2514_ = lean_box(0);
lean_inc_n(v___x_2506_, 4);
v___x_2515_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2506_);
lean_ctor_set(v___x_2515_, 1, v___x_2511_);
lean_ctor_set(v___x_2515_, 2, v___x_2513_);
lean_ctor_set(v___x_2515_, 3, v___x_2514_);
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2506_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2519_ = l_Lean_Syntax_node1(v___x_2506_, v___x_2518_, v_stx_1863_);
v___x_2520_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2506_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_Syntax_node4(v___x_2506_, v___x_1875_, v___x_2515_, v___x_2517_, v___x_2519_, v___x_2521_);
v___x_2523_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2522_);
lean_ctor_set(v___x_2528_, 1, v_a_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v___x_2522_);
v_a_2533_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2523_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2523_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v___x_2506_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2553_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2507_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2507_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2561_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2504_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2504_);
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
else
{
lean_object* v_val_2569_; lean_object* v___x_2570_; 
lean_dec(v_id_1862_);
v_val_2569_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2570_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2569_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v_pat_1868_ = v_a_2571_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_stx_1863_);
v_a_2572_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2570_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v_stx_2581_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2611_; lean_object* v___y_2612_; 
v___x_2580_ = lean_unsigned_to_nat(0u);
v_stx_2581_ = l_Lean_Syntax_getArg(v___x_2502_, v___x_2580_);
lean_dec(v___x_2502_);
v___x_2599_ = lean_unsigned_to_nat(2u);
v___x_2600_ = lean_unsigned_to_nat(3u);
v___x_2601_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2600_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2601_);
v___x_2760_ = l_Lean_Syntax_isOfKind(v___x_2601_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_dec(v___x_2601_);
lean_dec(v_stx_2581_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = l_Lean_SourceInfo_fromRef(v_a_2762_, v___x_2084_);
lean_dec(v_a_2762_);
v___x_2764_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v_a_2767_; lean_object* v_quotContext_x3f_2798_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v_quotContext_x3f_2798_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2798_) == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v_a_2767_ = v_a_2800_;
goto v___jp_2766_;
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2765_);
lean_dec(v___x_2763_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2801_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2799_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_val_2809_; 
v_val_2809_ = lean_ctor_get(v_quotContext_x3f_2798_, 0);
lean_inc(v_val_2809_);
v_a_2767_ = v_val_2809_;
goto v___jp_2766_;
}
v___jp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2768_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2769_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2770_ = l_Lean_addMacroScope(v_a_2767_, v___x_2769_, v_a_2765_);
v___x_2771_ = lean_box(0);
lean_inc_n(v___x_2763_, 4);
v___x_2772_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2763_);
lean_ctor_set(v___x_2772_, 1, v___x_2768_);
lean_ctor_set(v___x_2772_, 2, v___x_2770_);
lean_ctor_set(v___x_2772_, 3, v___x_2771_);
v___x_2773_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2763_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2776_ = l_Lean_Syntax_node1(v___x_2763_, v___x_2775_, v_stx_1863_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2763_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = l_Lean_Syntax_node4(v___x_2763_, v___x_1875_, v___x_2772_, v___x_2774_, v___x_2776_, v___x_2778_);
v___x_2780_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2789_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2789_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2789_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2779_);
lean_ctor_set(v___x_2785_, 1, v_a_2781_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2785_);
v___x_2787_ = v___x_2783_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v___x_2779_);
v_a_2790_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2780_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2780_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v___x_2763_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2810_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2764_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2764_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2818_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2761_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2761_);
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
else
{
lean_object* v_val_2826_; lean_object* v___x_2827_; 
lean_dec(v_id_1862_);
v_val_2826_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2827_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2826_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v_pat_1868_ = v_a_2828_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_stx_1863_);
v_a_2829_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2827_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2827_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
else
{
goto v___jp_2662_;
}
}
else
{
goto v___jp_2662_;
}
v___jp_2582_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2588_ = lean_string_append(v___y_2586_, v___x_2587_);
lean_inc(v___y_2584_);
v___x_2589_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2584_, v_stx_2581_, v_id_1862_, v___x_2588_, v___y_2583_, v___y_2585_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v_pat_1868_ = v_a_2590_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_stx_1863_);
v_a_2591_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2589_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2589_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
v___jp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2606_ = l_Lean_Syntax_isStrLit_x3f(v___x_2601_);
lean_dec(v___x_2601_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2608_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2607_);
v___y_2583_ = v___y_2603_;
v___y_2584_ = v___x_2605_;
v___y_2585_ = v___y_2604_;
v___y_2586_ = v___x_2608_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2609_; 
v_val_2609_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v___x_2606_, 1);
v___y_2583_ = v___y_2603_;
v___y_2584_ = v___x_2605_;
v___y_2585_ = v___y_2604_;
v___y_2586_ = v_val_2609_;
goto v___jp_2582_;
}
}
v___jp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = lean_unsigned_to_nat(5u);
v___x_2614_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2613_);
v___x_2615_ = l_Lean_Syntax_isNone(v___x_2614_);
if (v___x_2615_ == 0)
{
uint8_t v___x_2616_; 
v___x_2616_ = l_Lean_Syntax_matchesNull(v___x_2614_, v___x_2599_);
if (v___x_2616_ == 0)
{
lean_dec(v___x_2601_);
lean_dec(v_stx_2581_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_Elab_Command_getRef___redArg(v___y_2611_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = l_Lean_SourceInfo_fromRef(v_a_2618_, v___x_2616_);
lean_dec(v_a_2618_);
v___x_2620_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2611_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_quotContext_x3f_2621_; 
v_quotContext_x3f_2621_ = lean_ctor_get(v___y_2611_, 5);
if (lean_obj_tag(v_quotContext_x3f_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2623_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2612_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___y_1981_ = v___y_2611_;
v___y_1982_ = v_a_2622_;
v___y_1983_ = v___y_2612_;
v___y_1984_ = v___x_2619_;
v_a_1985_ = v_a_2624_;
goto v___jp_1980_;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2622_);
lean_dec(v___x_2619_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2625_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2623_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2623_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v_val_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2620_, 1);
v_val_2634_ = lean_ctor_get(v_quotContext_x3f_2621_, 0);
lean_inc(v_val_2634_);
v___y_1981_ = v___y_2611_;
v___y_1982_ = v_a_2633_;
v___y_1983_ = v___y_2612_;
v___y_1984_ = v___x_2619_;
v_a_1985_ = v_val_2634_;
goto v___jp_1980_;
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v___x_2619_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2635_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2620_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2620_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2643_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2617_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2617_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_val_2651_; lean_object* v___x_2652_; 
lean_dec(v_id_1862_);
v_val_2651_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2652_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2651_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v_pat_1868_ = v_a_2653_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_stx_1863_);
v_a_2654_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2652_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2652_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1861_);
v___y_2603_ = v___y_2611_;
v___y_2604_ = v___y_2612_;
goto v___jp_2602_;
}
}
else
{
lean_dec(v___x_2614_);
lean_dec(v_id_x3f_1861_);
v___y_2603_ = v___y_2611_;
v___y_2604_ = v___y_2612_;
goto v___jp_2602_;
}
}
v___jp_2662_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2663_ = lean_unsigned_to_nat(4u);
v___x_2664_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2663_);
v___x_2665_ = l_Lean_Syntax_isNone(v___x_2664_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; 
lean_inc(v___x_2664_);
v___x_2666_ = l_Lean_Syntax_matchesNull(v___x_2664_, v___x_2599_);
if (v___x_2666_ == 0)
{
lean_dec(v___x_2664_);
lean_dec(v___x_2601_);
lean_dec(v_stx_2581_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = l_Lean_SourceInfo_fromRef(v_a_2668_, v___x_2666_);
lean_dec(v_a_2668_);
v___x_2670_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_quotContext_x3f_2671_; 
v_quotContext_x3f_2671_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; 
v_a_2672_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2673_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___y_2017_ = v_a_2672_;
v___y_2018_ = v___x_2669_;
v_a_2019_ = v_a_2674_;
goto v___jp_2016_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2672_);
lean_dec(v___x_2669_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2675_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2673_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2673_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v_val_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2670_, 1);
v_val_2684_ = lean_ctor_get(v_quotContext_x3f_2671_, 0);
lean_inc(v_val_2684_);
v___y_2017_ = v_a_2683_;
v___y_2018_ = v___x_2669_;
v_a_2019_ = v_val_2684_;
goto v___jp_2016_;
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v___x_2669_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2685_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2670_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2670_);
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
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2693_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2667_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2667_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v_val_2701_; lean_object* v___x_2702_; 
lean_dec(v_id_1862_);
v_val_2701_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2701_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2702_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2701_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v_pat_1868_ = v_a_2703_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_stx_1863_);
v_a_2704_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2702_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
else
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = l_Lean_Syntax_getArg(v___x_2664_, v___x_2501_);
lean_dec(v___x_2664_);
v___x_2713_ = l_Lean_Syntax_matchesNull(v___x_2712_, v___x_2501_);
if (v___x_2713_ == 0)
{
lean_dec(v___x_2601_);
lean_dec(v_stx_2581_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2716_ = l_Lean_SourceInfo_fromRef(v_a_2715_, v___x_2713_);
lean_dec(v_a_2715_);
v___x_2717_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_quotContext_x3f_2718_; 
v_quotContext_x3f_2718_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2720_; 
v_a_2719_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2720_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2051_ = v_a_2719_;
v___y_2052_ = v___x_2716_;
v_a_2053_ = v_a_2721_;
goto v___jp_2050_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2719_);
lean_dec(v___x_2716_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2722_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2720_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2720_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v_val_2731_; 
v_a_2730_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2717_, 1);
v_val_2731_ = lean_ctor_get(v_quotContext_x3f_2718_, 0);
lean_inc(v_val_2731_);
v___y_2051_ = v_a_2730_;
v___y_2052_ = v___x_2716_;
v_a_2053_ = v_val_2731_;
goto v___jp_2050_;
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v___x_2716_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2732_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2717_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2717_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2740_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2714_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2714_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
else
{
lean_object* v_val_2748_; lean_object* v___x_2749_; 
lean_dec(v_id_1862_);
v_val_2748_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2748_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2749_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2748_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v_pat_1868_ = v_a_2750_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_stx_1863_);
v_a_2751_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2749_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2749_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
v___y_2611_ = v_a_1864_;
v___y_2612_ = v_a_1865_;
goto v___jp_2610_;
}
}
}
else
{
lean_dec(v___x_2664_);
v___y_2611_ = v_a_1864_;
v___y_2612_ = v_a_1865_;
goto v___jp_2610_;
}
}
}
}
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2837_);
v___x_2839_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2840_ = l_Lean_Syntax_matchesIdent(v___x_2838_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2842_ = l_Lean_Syntax_matchesIdent(v___x_2838_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2844_ = l_Lean_Syntax_matchesIdent(v___x_2838_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2846_ = l_Lean_Syntax_matchesIdent(v___x_2838_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2848_ = l_Lean_Syntax_matchesIdent(v___x_2838_, v___x_2847_);
lean_dec(v___x_2838_);
if (v___x_2848_ == 0)
{
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l_Lean_SourceInfo_fromRef(v_a_2850_, v___x_2848_);
lean_dec(v_a_2850_);
v___x_2852_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v_a_2855_; lean_object* v_quotContext_x3f_2886_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v_quotContext_x3f_2886_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2886_) == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v_a_2855_ = v_a_2888_;
goto v___jp_2854_;
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v_a_2853_);
lean_dec(v___x_2851_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2889_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2887_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2887_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v_val_2897_; 
v_val_2897_ = lean_ctor_get(v_quotContext_x3f_2886_, 0);
lean_inc(v_val_2897_);
v_a_2855_ = v_val_2897_;
goto v___jp_2854_;
}
v___jp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2856_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2857_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2858_ = l_Lean_addMacroScope(v_a_2855_, v___x_2857_, v_a_2853_);
v___x_2859_ = lean_box(0);
lean_inc_n(v___x_2851_, 4);
v___x_2860_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2851_);
lean_ctor_set(v___x_2860_, 1, v___x_2856_);
lean_ctor_set(v___x_2860_, 2, v___x_2858_);
lean_ctor_set(v___x_2860_, 3, v___x_2859_);
v___x_2861_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2851_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2864_ = l_Lean_Syntax_node1(v___x_2851_, v___x_2863_, v_stx_1863_);
v___x_2865_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2851_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_Syntax_node4(v___x_2851_, v___x_1875_, v___x_2860_, v___x_2862_, v___x_2864_, v___x_2866_);
v___x_2868_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2877_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2877_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2877_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2867_);
lean_ctor_set(v___x_2873_, 1, v_a_2869_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2873_);
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v___x_2867_);
v_a_2878_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2868_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2868_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v___x_2851_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2898_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2852_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2852_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2906_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2849_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2849_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_val_2914_; lean_object* v___x_2915_; 
lean_dec(v_id_1862_);
v_val_2914_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2915_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2914_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v_pat_1868_ = v_a_2916_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_stx_1863_);
v_a_2917_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2915_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2915_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_unsigned_to_nat(2u);
v___x_2927_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_2926_);
lean_inc(v___x_2927_);
v___x_2928_ = l_Lean_Syntax_matchesNull(v___x_2927_, v___x_2925_);
if (v___x_2928_ == 0)
{
lean_dec(v___x_2927_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2931_ = l_Lean_SourceInfo_fromRef(v_a_2930_, v___x_2928_);
lean_dec(v_a_2930_);
v___x_2932_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v_a_2935_; lean_object* v_quotContext_x3f_2966_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v_quotContext_x3f_2966_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_2966_) == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v_a_2935_ = v_a_2968_;
goto v___jp_2934_;
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_a_2933_);
lean_dec(v___x_2931_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2969_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2967_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2967_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_val_2977_; 
v_val_2977_ = lean_ctor_get(v_quotContext_x3f_2966_, 0);
lean_inc(v_val_2977_);
v_a_2935_ = v_val_2977_;
goto v___jp_2934_;
}
v___jp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2936_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2937_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2938_ = l_Lean_addMacroScope(v_a_2935_, v___x_2937_, v_a_2933_);
v___x_2939_ = lean_box(0);
lean_inc_n(v___x_2931_, 4);
v___x_2940_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2931_);
lean_ctor_set(v___x_2940_, 1, v___x_2936_);
lean_ctor_set(v___x_2940_, 2, v___x_2938_);
lean_ctor_set(v___x_2940_, 3, v___x_2939_);
v___x_2941_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2931_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2944_ = l_Lean_Syntax_node1(v___x_2931_, v___x_2943_, v_stx_1863_);
v___x_2945_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2931_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = l_Lean_Syntax_node4(v___x_2931_, v___x_1875_, v___x_2940_, v___x_2942_, v___x_2944_, v___x_2946_);
v___x_2948_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2957_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2957_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2957_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2947_);
lean_ctor_set(v___x_2953_, 1, v_a_2949_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2955_ = v___x_2951_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v___x_2947_);
v_a_2958_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2948_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2948_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v___x_2931_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2978_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2932_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2932_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_2986_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2929_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2929_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v_val_2994_; lean_object* v___x_2995_; 
lean_dec(v_id_1862_);
v_val_2994_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_2994_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_2995_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_2994_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_pat_1868_ = v_a_2996_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v_stx_1863_);
v_a_2997_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2995_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
else
{
lean_object* v_stx_3005_; lean_object* v___x_3006_; 
lean_dec(v_stx_1863_);
v_stx_3005_ = l_Lean_Syntax_getArg(v___x_2927_, v___x_2837_);
lean_dec(v___x_2927_);
v___x_3006_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1861_, v_id_1862_, v_stx_3005_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_fst_3008_; lean_object* v_snd_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3069_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v_fst_3008_ = lean_ctor_get(v_a_3007_, 0);
v_snd_3009_ = lean_ctor_get(v_a_3007_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_a_3007_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3011_ = v_a_3007_;
v_isShared_3012_ = v_isSharedCheck_3069_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snd_3009_);
lean_inc(v_fst_3008_);
lean_dec(v_a_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3069_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = l_Lean_SourceInfo_fromRef(v_a_3014_, v___x_2846_);
lean_dec(v_a_3014_);
v___x_3016_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3052_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3052_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3052_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v_a_3022_; lean_object* v_quotContext_x3f_3040_; 
v_quotContext_x3f_3040_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3040_) == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v_a_3022_ = v_a_3042_;
goto v___jp_3021_;
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_del_object(v___x_3019_);
lean_dec(v_a_3017_);
lean_dec(v___x_3015_);
lean_del_object(v___x_3011_);
lean_dec(v_snd_3009_);
lean_dec(v_fst_3008_);
v_a_3043_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3041_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3041_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v_val_3051_; 
v_val_3051_ = lean_ctor_get(v_quotContext_x3f_3040_, 0);
lean_inc(v_val_3051_);
v_a_3022_ = v_val_3051_;
goto v___jp_3021_;
}
v___jp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3023_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_3024_ = l_Lean_addMacroScope(v_a_3022_, v___x_2847_, v_a_3017_);
v___x_3025_ = lean_box(0);
lean_inc_n(v___x_3015_, 4);
v___x_3026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3015_);
lean_ctor_set(v___x_3026_, 1, v___x_3023_);
lean_ctor_set(v___x_3026_, 2, v___x_3024_);
lean_ctor_set(v___x_3026_, 3, v___x_3025_);
v___x_3027_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3015_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_3030_ = l_Lean_Syntax_node1(v___x_3015_, v___x_3029_, v_fst_3008_);
v___x_3031_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3015_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Lean_Syntax_node4(v___x_3015_, v___x_1875_, v___x_3026_, v___x_3028_, v___x_3030_, v___x_3032_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3033_);
v___x_3035_ = v___x_3011_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_snd_3009_);
v___x_3035_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3037_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3035_);
v___x_3037_ = v___x_3019_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v___x_3015_);
lean_del_object(v___x_3011_);
lean_dec(v_snd_3009_);
lean_dec(v_fst_3008_);
v_a_3053_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3016_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3016_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_del_object(v___x_3011_);
lean_dec(v_snd_3009_);
lean_dec(v_fst_3008_);
v_a_3061_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3013_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3013_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
lean_dec(v___x_2838_);
v___x_3070_ = lean_unsigned_to_nat(1u);
v___x_3071_ = lean_unsigned_to_nat(2u);
v___x_3072_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_3071_);
lean_inc(v___x_3072_);
v___x_3073_ = l_Lean_Syntax_matchesNull(v___x_3072_, v___x_3070_);
if (v___x_3073_ == 0)
{
lean_dec(v___x_3072_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
v___x_3076_ = l_Lean_SourceInfo_fromRef(v_a_3075_, v___x_3073_);
lean_dec(v_a_3075_);
v___x_3077_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v_a_3080_; lean_object* v_quotContext_x3f_3111_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v_quotContext_x3f_3111_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3111_) == 0)
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v_a_3080_ = v_a_3113_;
goto v___jp_3079_;
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_a_3078_);
lean_dec(v___x_3076_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3114_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3112_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3112_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_val_3122_; 
v_val_3122_ = lean_ctor_get(v_quotContext_x3f_3111_, 0);
lean_inc(v_val_3122_);
v_a_3080_ = v_val_3122_;
goto v___jp_3079_;
}
v___jp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3081_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3083_ = l_Lean_addMacroScope(v_a_3080_, v___x_3082_, v_a_3078_);
v___x_3084_ = lean_box(0);
lean_inc_n(v___x_3076_, 4);
v___x_3085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3076_);
lean_ctor_set(v___x_3085_, 1, v___x_3081_);
lean_ctor_set(v___x_3085_, 2, v___x_3083_);
lean_ctor_set(v___x_3085_, 3, v___x_3084_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3076_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3089_ = l_Lean_Syntax_node1(v___x_3076_, v___x_3088_, v_stx_1863_);
v___x_3090_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3076_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = l_Lean_Syntax_node4(v___x_3076_, v___x_1875_, v___x_3085_, v___x_3087_, v___x_3089_, v___x_3091_);
v___x_3093_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3092_);
lean_ctor_set(v___x_3098_, 1, v_a_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v___x_3092_);
v_a_3103_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3093_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3093_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v___x_3076_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3123_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3077_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3077_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3131_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3074_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3074_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3140_; 
lean_dec(v_id_1862_);
v_val_3139_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3140_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3139_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v_pat_1868_ = v_a_3141_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_stx_1863_);
v_a_3142_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3140_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3140_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3150_ = l_Lean_Syntax_getArg(v___x_3072_, v___x_2837_);
lean_dec(v___x_3072_);
v___x_3151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3150_);
v___x_3152_ = l_Lean_Syntax_isOfKind(v___x_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_dec(v___x_3150_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = l_Lean_SourceInfo_fromRef(v_a_3154_, v___x_3152_);
lean_dec(v_a_3154_);
v___x_3156_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v_a_3159_; lean_object* v_quotContext_x3f_3190_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v_quotContext_x3f_3190_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3190_) == 0)
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v_a_3159_ = v_a_3192_;
goto v___jp_3158_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3157_);
lean_dec(v___x_3155_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3193_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3191_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3191_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_val_3201_; 
v_val_3201_ = lean_ctor_get(v_quotContext_x3f_3190_, 0);
lean_inc(v_val_3201_);
v_a_3159_ = v_val_3201_;
goto v___jp_3158_;
}
v___jp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3160_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3161_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3162_ = l_Lean_addMacroScope(v_a_3159_, v___x_3161_, v_a_3157_);
v___x_3163_ = lean_box(0);
lean_inc_n(v___x_3155_, 4);
v___x_3164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3155_);
lean_ctor_set(v___x_3164_, 1, v___x_3160_);
lean_ctor_set(v___x_3164_, 2, v___x_3162_);
lean_ctor_set(v___x_3164_, 3, v___x_3163_);
v___x_3165_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3155_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3168_ = l_Lean_Syntax_node1(v___x_3155_, v___x_3167_, v_stx_1863_);
v___x_3169_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3155_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_node4(v___x_3155_, v___x_1875_, v___x_3164_, v___x_3166_, v___x_3168_, v___x_3170_);
v___x_3172_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3181_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3171_);
lean_ctor_set(v___x_3177_, 1, v_a_3173_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3177_);
v___x_3179_ = v___x_3175_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v___x_3171_);
v_a_3182_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3172_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3172_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v___x_3155_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3202_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3156_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3156_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3210_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3153_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3153_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_val_3218_; lean_object* v___x_3219_; 
lean_dec(v_id_1862_);
v_val_3218_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3219_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3218_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v_pat_1868_ = v_a_3220_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_stx_1863_);
v_a_3221_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3219_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3219_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
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
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = l_Lean_Syntax_getArg(v___x_3150_, v___x_2837_);
v___x_3230_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3231_ = l_Lean_Syntax_matchesIdent(v___x_3229_, v___x_3230_);
lean_dec(v___x_3229_);
if (v___x_3231_ == 0)
{
lean_dec(v___x_3150_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_Lean_SourceInfo_fromRef(v_a_3233_, v___x_3231_);
lean_dec(v_a_3233_);
v___x_3235_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v_a_3238_; lean_object* v_quotContext_x3f_3269_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v_quotContext_x3f_3269_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3269_) == 0)
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v_a_3238_ = v_a_3271_;
goto v___jp_3237_;
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec(v_a_3236_);
lean_dec(v___x_3234_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3272_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3270_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3270_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
lean_object* v_val_3280_; 
v_val_3280_ = lean_ctor_get(v_quotContext_x3f_3269_, 0);
lean_inc(v_val_3280_);
v_a_3238_ = v_val_3280_;
goto v___jp_3237_;
}
v___jp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3239_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3240_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3241_ = l_Lean_addMacroScope(v_a_3238_, v___x_3240_, v_a_3236_);
v___x_3242_ = lean_box(0);
lean_inc_n(v___x_3234_, 4);
v___x_3243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3234_);
lean_ctor_set(v___x_3243_, 1, v___x_3239_);
lean_ctor_set(v___x_3243_, 2, v___x_3241_);
lean_ctor_set(v___x_3243_, 3, v___x_3242_);
v___x_3244_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3234_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3247_ = l_Lean_Syntax_node1(v___x_3234_, v___x_3246_, v_stx_1863_);
v___x_3248_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3234_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_Syntax_node4(v___x_3234_, v___x_1875_, v___x_3243_, v___x_3245_, v___x_3247_, v___x_3249_);
v___x_3251_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3260_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3250_);
lean_ctor_set(v___x_3256_, 1, v_a_3252_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3256_);
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v___x_3250_);
v_a_3261_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3251_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3251_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v___x_3234_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3281_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3235_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3235_);
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
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3289_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3232_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3232_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
lean_object* v_val_3297_; lean_object* v___x_3298_; 
lean_dec(v_id_1862_);
v_val_3297_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3298_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3297_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v_pat_1868_ = v_a_3299_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v_stx_1863_);
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
}
else
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = l_Lean_Syntax_getArg(v___x_3150_, v___x_3070_);
lean_dec(v___x_3150_);
v___x_3309_ = l_Lean_Syntax_matchesNull(v___x_3308_, v___x_2837_);
if (v___x_3309_ == 0)
{
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v___x_3312_ = l_Lean_SourceInfo_fromRef(v_a_3311_, v___x_3309_);
lean_dec(v_a_3311_);
v___x_3313_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v_a_3316_; lean_object* v_quotContext_x3f_3347_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v_quotContext_x3f_3347_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3347_) == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v_a_3316_ = v_a_3349_;
goto v___jp_3315_;
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v_a_3314_);
lean_dec(v___x_3312_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3350_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3348_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_val_3358_; 
v_val_3358_ = lean_ctor_get(v_quotContext_x3f_3347_, 0);
lean_inc(v_val_3358_);
v_a_3316_ = v_val_3358_;
goto v___jp_3315_;
}
v___jp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3317_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3319_ = l_Lean_addMacroScope(v_a_3316_, v___x_3318_, v_a_3314_);
v___x_3320_ = lean_box(0);
lean_inc_n(v___x_3312_, 4);
v___x_3321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3312_);
lean_ctor_set(v___x_3321_, 1, v___x_3317_);
lean_ctor_set(v___x_3321_, 2, v___x_3319_);
lean_ctor_set(v___x_3321_, 3, v___x_3320_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3312_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3325_ = l_Lean_Syntax_node1(v___x_3312_, v___x_3324_, v_stx_1863_);
v___x_3326_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3312_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_Syntax_node4(v___x_3312_, v___x_1875_, v___x_3321_, v___x_3323_, v___x_3325_, v___x_3327_);
v___x_3329_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3338_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3338_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3338_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3328_);
lean_ctor_set(v___x_3334_, 1, v_a_3330_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3334_);
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
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
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec(v___x_3328_);
v_a_3339_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3329_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3329_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v___x_3312_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3359_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3313_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3313_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3367_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3310_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3310_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v_val_3375_; lean_object* v___x_3376_; 
lean_dec(v_id_1862_);
v_val_3375_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3376_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3375_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v_pat_1868_ = v_a_3377_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec(v_stx_1863_);
v_a_3378_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3376_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3376_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec(v_id_x3f_1861_);
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3387_ = lean_box(0);
v___x_3388_ = l_Lean_Syntax_mkAntiquotNode(v___x_3386_, v_id_1862_, v___x_2837_, v___x_3387_, v___x_2844_);
v_pat_1868_ = v___x_3388_;
goto v___jp_1867_;
}
}
}
}
}
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
lean_dec(v___x_2838_);
v___x_3389_ = lean_unsigned_to_nat(1u);
v___x_3390_ = lean_unsigned_to_nat(2u);
v___x_3391_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_3390_);
lean_inc(v___x_3391_);
v___x_3392_ = l_Lean_Syntax_matchesNull(v___x_3391_, v___x_3389_);
if (v___x_3392_ == 0)
{
lean_dec(v___x_3391_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = l_Lean_SourceInfo_fromRef(v_a_3394_, v___x_3392_);
lean_dec(v_a_3394_);
v___x_3396_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v_a_3399_; lean_object* v_quotContext_x3f_3430_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v_quotContext_x3f_3430_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3430_) == 0)
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v_a_3399_ = v_a_3432_;
goto v___jp_3398_;
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v_a_3397_);
lean_dec(v___x_3395_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3433_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3431_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3431_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
else
{
lean_object* v_val_3441_; 
v_val_3441_ = lean_ctor_get(v_quotContext_x3f_3430_, 0);
lean_inc(v_val_3441_);
v_a_3399_ = v_val_3441_;
goto v___jp_3398_;
}
v___jp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3400_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3401_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3402_ = l_Lean_addMacroScope(v_a_3399_, v___x_3401_, v_a_3397_);
v___x_3403_ = lean_box(0);
lean_inc_n(v___x_3395_, 4);
v___x_3404_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3395_);
lean_ctor_set(v___x_3404_, 1, v___x_3400_);
lean_ctor_set(v___x_3404_, 2, v___x_3402_);
lean_ctor_set(v___x_3404_, 3, v___x_3403_);
v___x_3405_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3395_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3408_ = l_Lean_Syntax_node1(v___x_3395_, v___x_3407_, v_stx_1863_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3395_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = l_Lean_Syntax_node4(v___x_3395_, v___x_1875_, v___x_3404_, v___x_3406_, v___x_3408_, v___x_3410_);
v___x_3412_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3421_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3421_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3421_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3411_);
lean_ctor_set(v___x_3417_, 1, v_a_3413_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3417_);
v___x_3419_ = v___x_3415_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v___x_3411_);
v_a_3422_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3412_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3412_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v___x_3395_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3442_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3396_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3396_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3450_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3393_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3393_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v_val_3458_; lean_object* v___x_3459_; 
lean_dec(v_id_1862_);
v_val_3458_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3458_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3459_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3458_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_pat_1868_ = v_a_3460_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_stx_1863_);
v_a_3461_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3459_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
else
{
lean_object* v_stx_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_id_x3f_1861_);
v_stx_3469_ = l_Lean_Syntax_getArg(v___x_3391_, v___x_2837_);
lean_dec(v___x_3391_);
v___x_3470_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3471_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2841_, v_stx_3469_, v_id_1862_, v___x_3470_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v_pat_1868_ = v_a_3472_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_stx_1863_);
v_a_3473_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3471_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3471_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
lean_dec(v___x_2838_);
v___x_3481_ = lean_unsigned_to_nat(1u);
v___x_3482_ = lean_unsigned_to_nat(2u);
v___x_3483_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_3482_);
lean_inc(v___x_3483_);
v___x_3484_ = l_Lean_Syntax_matchesNull(v___x_3483_, v___x_3481_);
if (v___x_3484_ == 0)
{
lean_dec(v___x_3483_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = l_Lean_SourceInfo_fromRef(v_a_3486_, v___x_3484_);
lean_dec(v_a_3486_);
v___x_3488_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_a_3491_; lean_object* v_quotContext_x3f_3522_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v_quotContext_x3f_3522_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3522_) == 0)
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v_a_3491_ = v_a_3524_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_a_3489_);
lean_dec(v___x_3487_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3525_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3523_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3523_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_val_3533_; 
v_val_3533_ = lean_ctor_get(v_quotContext_x3f_3522_, 0);
lean_inc(v_val_3533_);
v_a_3491_ = v_val_3533_;
goto v___jp_3490_;
}
v___jp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3492_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3494_ = l_Lean_addMacroScope(v_a_3491_, v___x_3493_, v_a_3489_);
v___x_3495_ = lean_box(0);
lean_inc_n(v___x_3487_, 4);
v___x_3496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3487_);
lean_ctor_set(v___x_3496_, 1, v___x_3492_);
lean_ctor_set(v___x_3496_, 2, v___x_3494_);
lean_ctor_set(v___x_3496_, 3, v___x_3495_);
v___x_3497_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3487_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3500_ = l_Lean_Syntax_node1(v___x_3487_, v___x_3499_, v_stx_1863_);
v___x_3501_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3487_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_Syntax_node4(v___x_3487_, v___x_1875_, v___x_3496_, v___x_3498_, v___x_3500_, v___x_3502_);
v___x_3504_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3513_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3513_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3513_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3503_);
lean_ctor_set(v___x_3509_, 1, v_a_3505_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3509_);
v___x_3511_ = v___x_3507_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v___x_3503_);
v_a_3514_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3504_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3504_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v___x_3487_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3534_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3488_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3488_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3542_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3485_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3485_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_object* v_val_3550_; lean_object* v___x_3551_; 
lean_dec(v_id_1862_);
v_val_3550_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3550_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3551_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3550_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v_pat_1868_ = v_a_3552_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec(v_stx_1863_);
v_a_3553_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3551_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
else
{
lean_object* v_stx_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec(v_id_x3f_1861_);
v_stx_3561_ = l_Lean_Syntax_getArg(v___x_3483_, v___x_2837_);
lean_dec(v___x_3483_);
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3563_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2841_, v_stx_3561_, v_id_1862_, v___x_3562_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v_pat_1868_ = v_a_3564_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec(v_stx_1863_);
v_a_3565_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3563_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3563_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
lean_dec(v___x_2838_);
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_unsigned_to_nat(2u);
v___x_3575_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_3574_);
lean_inc(v___x_3575_);
v___x_3576_ = l_Lean_Syntax_matchesNull(v___x_3575_, v___x_3573_);
if (v___x_3576_ == 0)
{
lean_dec(v___x_3575_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_Lean_SourceInfo_fromRef(v_a_3578_, v___x_3576_);
lean_dec(v_a_3578_);
v___x_3580_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v_a_3583_; lean_object* v_quotContext_x3f_3614_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v_quotContext_x3f_3614_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3614_) == 0)
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v_a_3583_ = v_a_3616_;
goto v___jp_3582_;
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_a_3581_);
lean_dec(v___x_3579_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3617_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3615_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3615_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_val_3625_; 
v_val_3625_ = lean_ctor_get(v_quotContext_x3f_3614_, 0);
lean_inc(v_val_3625_);
v_a_3583_ = v_val_3625_;
goto v___jp_3582_;
}
v___jp_3582_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3584_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3585_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3586_ = l_Lean_addMacroScope(v_a_3583_, v___x_3585_, v_a_3581_);
v___x_3587_ = lean_box(0);
lean_inc_n(v___x_3579_, 4);
v___x_3588_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3579_);
lean_ctor_set(v___x_3588_, 1, v___x_3584_);
lean_ctor_set(v___x_3588_, 2, v___x_3586_);
lean_ctor_set(v___x_3588_, 3, v___x_3587_);
v___x_3589_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3579_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3592_ = l_Lean_Syntax_node1(v___x_3579_, v___x_3591_, v_stx_1863_);
v___x_3593_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3579_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = l_Lean_Syntax_node4(v___x_3579_, v___x_1875_, v___x_3588_, v___x_3590_, v___x_3592_, v___x_3594_);
v___x_3596_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3595_);
lean_ctor_set(v___x_3601_, 1, v_a_3597_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3601_);
v___x_3603_ = v___x_3599_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v___x_3595_);
v_a_3606_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3596_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3596_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v___x_3579_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3626_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3580_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3580_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3634_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3577_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3577_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3643_; 
lean_dec(v_id_1862_);
v_val_3642_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3643_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3642_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v_pat_1868_ = v_a_3644_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_stx_1863_);
v_a_3645_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3643_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3643_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
else
{
lean_object* v_stx_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_id_x3f_1861_);
v_stx_3653_ = l_Lean_Syntax_getArg(v___x_3575_, v___x_2837_);
lean_dec(v___x_3575_);
v___x_3654_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3655_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2839_, v_stx_3653_, v_id_1862_, v___x_3654_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v_pat_1868_ = v_a_3656_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec(v_stx_1863_);
v_a_3657_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3655_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3655_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
}
v___jp_1876_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1882_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1883_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1884_ = l_Lean_addMacroScope(v_a_1881_, v___x_1883_, v___y_1877_);
v___x_1885_ = lean_box(0);
lean_inc_n(v___y_1878_, 4);
v___x_1886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1886_, 0, v___y_1878_);
lean_ctor_set(v___x_1886_, 1, v___x_1882_);
lean_ctor_set(v___x_1886_, 2, v___x_1884_);
lean_ctor_set(v___x_1886_, 3, v___x_1885_);
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___y_1878_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_1890_ = l_Lean_Syntax_node1(v___y_1878_, v___x_1889_, v_stx_1863_);
v___x_1891_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___y_1878_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_Syntax_node4(v___y_1878_, v___x_1875_, v___x_1886_, v___x_1888_, v___x_1890_, v___x_1892_);
v___x_1894_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v___y_1880_, v___y_1879_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1893_);
lean_ctor_set(v___x_1899_, 1, v_a_1895_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v___x_1893_);
v_a_1904_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1894_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1894_);
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
v___jp_1912_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1916_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1917_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1918_ = l_Lean_addMacroScope(v_a_1915_, v___x_1917_, v___y_1913_);
v___x_1919_ = lean_box(0);
lean_inc_n(v___y_1914_, 4);
v___x_1920_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1920_, 0, v___y_1914_);
lean_ctor_set(v___x_1920_, 1, v___x_1916_);
lean_ctor_set(v___x_1920_, 2, v___x_1918_);
lean_ctor_set(v___x_1920_, 3, v___x_1919_);
v___x_1921_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1914_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_1924_ = l_Lean_Syntax_node1(v___y_1914_, v___x_1923_, v_stx_1863_);
v___x_1925_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1914_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l_Lean_Syntax_node4(v___y_1914_, v___x_1875_, v___x_1920_, v___x_1922_, v___x_1924_, v___x_1926_);
v___x_1928_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1927_);
lean_ctor_set(v___x_1933_, 1, v_a_1929_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v___x_1927_);
v_a_1938_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1928_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1928_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
v___jp_1946_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1950_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1951_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1952_ = l_Lean_addMacroScope(v_a_1949_, v___x_1951_, v___y_1948_);
v___x_1953_ = lean_box(0);
lean_inc_n(v___y_1947_, 4);
v___x_1954_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1954_, 0, v___y_1947_);
lean_ctor_set(v___x_1954_, 1, v___x_1950_);
lean_ctor_set(v___x_1954_, 2, v___x_1952_);
lean_ctor_set(v___x_1954_, 3, v___x_1953_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___y_1947_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_1958_ = l_Lean_Syntax_node1(v___y_1947_, v___x_1957_, v_stx_1863_);
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1947_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = l_Lean_Syntax_node4(v___y_1947_, v___x_1875_, v___x_1954_, v___x_1956_, v___x_1958_, v___x_1960_);
v___x_1962_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1961_);
lean_ctor_set(v___x_1967_, 1, v_a_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1967_);
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v___x_1961_);
v_a_1972_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1962_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1962_);
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
v___jp_1980_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1986_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1987_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1988_ = l_Lean_addMacroScope(v_a_1985_, v___x_1987_, v___y_1982_);
v___x_1989_ = lean_box(0);
lean_inc_n(v___y_1984_, 4);
v___x_1990_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1984_);
lean_ctor_set(v___x_1990_, 1, v___x_1986_);
lean_ctor_set(v___x_1990_, 2, v___x_1988_);
lean_ctor_set(v___x_1990_, 3, v___x_1989_);
v___x_1991_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1984_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_1994_ = l_Lean_Syntax_node1(v___y_1984_, v___x_1993_, v_stx_1863_);
v___x_1995_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___y_1984_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_Syntax_node4(v___y_1984_, v___x_1875_, v___x_1990_, v___x_1992_, v___x_1994_, v___x_1996_);
v___x_1998_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v___y_1981_, v___y_1983_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1997_);
lean_ctor_set(v___x_2003_, 1, v_a_1999_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v___x_1997_);
v_a_2008_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1998_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1998_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
v___jp_2016_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2020_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2021_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2022_ = l_Lean_addMacroScope(v_a_2019_, v___x_2021_, v___y_2017_);
v___x_2023_ = lean_box(0);
lean_inc_n(v___y_2018_, 4);
v___x_2024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2024_, 0, v___y_2018_);
lean_ctor_set(v___x_2024_, 1, v___x_2020_);
lean_ctor_set(v___x_2024_, 2, v___x_2022_);
lean_ctor_set(v___x_2024_, 3, v___x_2023_);
v___x_2025_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___y_2018_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2028_ = l_Lean_Syntax_node1(v___y_2018_, v___x_2027_, v_stx_1863_);
v___x_2029_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___y_2018_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_Syntax_node4(v___y_2018_, v___x_1875_, v___x_2024_, v___x_2026_, v___x_2028_, v___x_2030_);
v___x_2032_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2041_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2031_);
lean_ctor_set(v___x_2037_, 1, v_a_2033_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v___x_2031_);
v_a_2042_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2032_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2032_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
v___jp_2050_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2054_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2056_ = l_Lean_addMacroScope(v_a_2053_, v___x_2055_, v___y_2051_);
v___x_2057_ = lean_box(0);
lean_inc_n(v___y_2052_, 4);
v___x_2058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2058_, 0, v___y_2052_);
lean_ctor_set(v___x_2058_, 1, v___x_2054_);
lean_ctor_set(v___x_2058_, 2, v___x_2056_);
lean_ctor_set(v___x_2058_, 3, v___x_2057_);
v___x_2059_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2052_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_2062_ = l_Lean_Syntax_node1(v___y_2052_, v___x_2061_, v_stx_1863_);
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___y_2052_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = l_Lean_Syntax_node4(v___y_2052_, v___x_1875_, v___x_2058_, v___x_2060_, v___x_2062_, v___x_2064_);
v___x_2066_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2065_);
lean_ctor_set(v___x_2071_, 1, v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v___x_2065_);
v_a_2076_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2066_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2066_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_unsigned_to_nat(1u);
v___x_3666_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_3665_);
if (v___x_1872_ == 0)
{
lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3690_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3666_);
v___x_3691_ = l_Lean_Syntax_isOfKind(v___x_3666_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_dec(v___x_3666_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v___x_3694_ = l_Lean_SourceInfo_fromRef(v_a_3693_, v___x_1872_);
lean_dec(v_a_3693_);
v___x_3695_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v_a_3698_; lean_object* v_quotContext_x3f_3730_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v_quotContext_x3f_3730_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3730_) == 0)
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v_a_3698_ = v_a_3732_;
goto v___jp_3697_;
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_a_3696_);
lean_dec(v___x_3694_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3733_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3731_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3731_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_val_3741_; 
v_val_3741_ = lean_ctor_get(v_quotContext_x3f_3730_, 0);
lean_inc(v_val_3741_);
v_a_3698_ = v_val_3741_;
goto v___jp_3697_;
}
v___jp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3700_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3701_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3702_ = l_Lean_addMacroScope(v_a_3698_, v___x_3701_, v_a_3696_);
v___x_3703_ = lean_box(0);
lean_inc_n(v___x_3694_, 4);
v___x_3704_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3694_);
lean_ctor_set(v___x_3704_, 1, v___x_3700_);
lean_ctor_set(v___x_3704_, 2, v___x_3702_);
lean_ctor_set(v___x_3704_, 3, v___x_3703_);
v___x_3705_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3694_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3708_ = l_Lean_Syntax_node1(v___x_3694_, v___x_3707_, v_stx_1863_);
v___x_3709_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3694_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = l_Lean_Syntax_node4(v___x_3694_, v___x_3699_, v___x_3704_, v___x_3706_, v___x_3708_, v___x_3710_);
v___x_3712_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3721_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3721_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3721_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3711_);
lean_ctor_set(v___x_3717_, 1, v_a_3713_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3717_);
v___x_3719_ = v___x_3715_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3717_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v___x_3711_);
v_a_3722_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3712_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3712_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v___x_3694_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3742_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3695_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3695_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3750_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3692_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3692_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_val_3758_; lean_object* v___x_3759_; 
lean_dec(v_id_1862_);
v_val_3758_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3758_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3759_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3758_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v_pat_1868_ = v_a_3760_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_stx_1863_);
v_a_3761_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3759_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3759_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1861_);
goto v___jp_3667_;
}
}
else
{
lean_dec(v_id_x3f_1861_);
goto v___jp_3667_;
}
v___jp_3667_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3668_, 0, v___x_3666_);
v___x_3669_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3668_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v___x_3671_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3672_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3673_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3674_ = lean_unsigned_to_nat(4u);
v___x_3675_ = lean_mk_empty_array_with_capacity(v___x_3674_);
v___x_3676_ = lean_array_push(v___x_3675_, v_a_3670_);
v___x_3677_ = lean_array_push(v___x_3676_, v___x_3672_);
v___x_3678_ = lean_array_push(v___x_3677_, v___x_3673_);
v___x_3679_ = lean_array_push(v___x_3678_, v_id_1862_);
v___x_3680_ = lean_box(2);
v___x_3681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___x_3671_);
lean_ctor_set(v___x_3681_, 2, v___x_3679_);
v_pat_1868_ = v___x_3681_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3682_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3669_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3669_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = l_Lean_Syntax_getArg(v_stx_1863_, v___x_3769_);
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3770_);
v___x_3772_ = l_Lean_Syntax_isOfKind(v___x_3770_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_dec(v___x_3770_);
if (lean_obj_tag(v_id_x3f_1861_) == 0)
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_Elab_Command_getRef___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v___x_3775_ = l_Lean_SourceInfo_fromRef(v_a_3774_, v___x_3772_);
lean_dec(v_a_3774_);
v___x_3776_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1864_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v_a_3779_; lean_object* v_quotContext_x3f_3811_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v_quotContext_x3f_3811_ = lean_ctor_get(v_a_1864_, 5);
if (lean_obj_tag(v_quotContext_x3f_3811_) == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1865_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v_a_3779_ = v_a_3813_;
goto v___jp_3778_;
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_a_3777_);
lean_dec(v___x_3775_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3814_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3812_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3812_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v_val_3822_; 
v_val_3822_ = lean_ctor_get(v_quotContext_x3f_3811_, 0);
lean_inc(v_val_3822_);
v_a_3779_ = v_val_3822_;
goto v___jp_3778_;
}
v___jp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3781_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3782_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3783_ = l_Lean_addMacroScope(v_a_3779_, v___x_3782_, v_a_3777_);
v___x_3784_ = lean_box(0);
lean_inc_n(v___x_3775_, 4);
v___x_3785_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3775_);
lean_ctor_set(v___x_3785_, 1, v___x_3781_);
lean_ctor_set(v___x_3785_, 2, v___x_3783_);
lean_ctor_set(v___x_3785_, 3, v___x_3784_);
v___x_3786_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3775_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1863_);
v___x_3789_ = l_Lean_Syntax_node1(v___x_3775_, v___x_3788_, v_stx_1863_);
v___x_3790_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3775_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_Lean_Syntax_node4(v___x_3775_, v___x_3780_, v___x_3785_, v___x_3787_, v___x_3789_, v___x_3791_);
v___x_3793_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_id_1862_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3802_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3792_);
lean_ctor_set(v___x_3798_, 1, v_a_3794_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3800_ = v___x_3796_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v___x_3792_);
v_a_3803_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3793_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3793_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec(v___x_3775_);
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3823_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3776_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3776_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3831_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3773_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3773_);
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
else
{
lean_object* v_val_3839_; lean_object* v___x_3840_; 
lean_dec(v_id_1862_);
v_val_3839_ = lean_ctor_get(v_id_x3f_1861_, 0);
lean_inc(v_val_3839_);
lean_dec_ref_known(v_id_x3f_1861_, 1);
lean_inc(v_stx_1863_);
v___x_3840_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1863_, v_val_3839_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v_pat_1868_ = v_a_3841_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec(v_stx_1863_);
v_a_3842_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3840_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3840_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec(v_id_x3f_1861_);
v___x_3850_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3850_, 0, v___x_3770_);
v___x_3851_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3850_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3854_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3855_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3856_ = lean_unsigned_to_nat(4u);
v___x_3857_ = lean_mk_empty_array_with_capacity(v___x_3856_);
v___x_3858_ = lean_array_push(v___x_3857_, v_a_3852_);
v___x_3859_ = lean_array_push(v___x_3858_, v___x_3854_);
v___x_3860_ = lean_array_push(v___x_3859_, v___x_3855_);
v___x_3861_ = lean_array_push(v___x_3860_, v_id_1862_);
v___x_3862_ = lean_box(2);
v___x_3863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v___x_3853_);
lean_ctor_set(v___x_3863_, 2, v___x_3861_);
v_pat_1868_ = v___x_3863_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_stx_1863_);
lean_dec(v_id_1862_);
v_a_3864_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3851_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3851_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
v___jp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_stx_1863_);
lean_ctor_set(v___x_1869_, 1, v_pat_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3872_, lean_object* v_id_3873_, lean_object* v_stx_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3872_, v_id_3873_, v_stx_3874_, v_a_3875_, v_a_3876_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3879_, lean_object* v_x_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3880_, v___y_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3884_, lean_object* v_x_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3884_, v_x_3885_, v___y_3886_, v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec_ref(v_x_3885_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3889_, lean_object* v_ref_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3890_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3895_, lean_object* v_ref_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3895_, v_ref_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3911_, lean_object* v_x_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3912_, v___y_3913_, v___y_3914_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3917_, lean_object* v_x_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3917_, v_x_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3923_, lean_object* v_as_x27_3924_, lean_object* v_b_3925_, lean_object* v_a_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3924_, v_b_3925_, v___y_3927_, v___y_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3931_, lean_object* v_as_x27_3932_, lean_object* v_b_3933_, lean_object* v_a_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3931_, v_as_x27_3932_, v_b_3933_, v_a_3934_, v___y_3935_, v___y_3936_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v_as_x27_3932_);
lean_dec(v_as_3931_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3939_, lean_object* v_ref_3940_, lean_object* v_msg_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3940_, v_msg_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3946_, lean_object* v_ref_3947_, lean_object* v_msg_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3946_, v_ref_3947_, v_msg_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v_ref_3947_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3953_, lean_object* v_m_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3954_, v_a_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3957_, lean_object* v_m_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3957_, v_m_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_m_3958_);
return v_res_3960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3961_, lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
uint8_t v___x_3964_; 
v___x_3964_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3962_, v_x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3965_, lean_object* v_x_3966_, lean_object* v_x_3967_){
_start:
{
uint8_t v_res_3968_; lean_object* v_r_3969_; 
v_res_3968_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_3965_, v_x_3966_, v_x_3967_);
lean_dec_ref(v_x_3967_);
lean_dec_ref(v_x_3966_);
v_r_3969_ = lean_box(v_res_3968_);
return v_r_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3970_, lean_object* v_a_3971_, lean_object* v_x_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_3971_, v_x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3974_, lean_object* v_a_3975_, lean_object* v_x_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_3974_, v_a_3975_, v_x_3976_);
lean_dec(v_x_3976_);
lean_dec(v_a_3975_);
return v_res_3977_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3978_, lean_object* v_x_3979_, size_t v_x_3980_, lean_object* v_x_3981_){
_start:
{
uint8_t v___x_3982_; 
v___x_3982_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_3979_, v_x_3980_, v_x_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3983_, lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
size_t v_x_48320__boxed_3987_; uint8_t v_res_3988_; lean_object* v_r_3989_; 
v_x_48320__boxed_3987_ = lean_unbox_usize(v_x_3985_);
lean_dec(v_x_3985_);
v_res_3988_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_3983_, v_x_3984_, v_x_48320__boxed_3987_, v_x_3986_);
lean_dec_ref(v_x_3986_);
lean_dec_ref(v_x_3984_);
v_r_3989_ = lean_box(v_res_3988_);
return v_r_3989_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_3990_, lean_object* v_keys_3991_, lean_object* v_vals_3992_, lean_object* v_heq_3993_, lean_object* v_i_3994_, lean_object* v_k_3995_){
_start:
{
uint8_t v___x_3996_; 
v___x_3996_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_3991_, v_i_3994_, v_k_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3997_, lean_object* v_keys_3998_, lean_object* v_vals_3999_, lean_object* v_heq_4000_, lean_object* v_i_4001_, lean_object* v_k_4002_){
_start:
{
uint8_t v_res_4003_; lean_object* v_r_4004_; 
v_res_4003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_3997_, v_keys_3998_, v_vals_3999_, v_heq_4000_, v_i_4001_, v_k_4002_);
lean_dec_ref(v_k_4002_);
lean_dec_ref(v_vals_3999_);
lean_dec_ref(v_keys_3998_);
v_r_4004_ = lean_box(v_res_4003_);
return v_r_4004_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_k_4011_){
_start:
{
lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4012_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_4013_ = lean_name_eq(v_k_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
v___x_4014_ = 1;
return v___x_4014_;
}
else
{
uint8_t v___x_4015_; 
v___x_4015_ = 0;
return v___x_4015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_k_4016_){
_start:
{
uint8_t v_res_4017_; lean_object* v_r_4018_; 
v_res_4017_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_4016_);
lean_dec(v_k_4016_);
v_r_4018_ = lean_box(v_res_4017_);
return v_r_4018_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_4029_ = l_String_toRawSubstring_x27(v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v___f_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___f_4036_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_4037_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_4037_, 0, v_stx_4032_);
lean_closure_set(v___x_4037_, 1, v___f_4036_);
v___x_4038_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_4037_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc_n(v_a_4039_, 2);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4040_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_4041_ = l_Lean_Syntax_isOfKind(v_a_4039_, v___x_4040_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_a_4039_);
v___x_4042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = l_Lean_Syntax_getArg(v_a_4039_, v___x_4051_);
v___x_4053_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4052_);
v___x_4054_ = l_Lean_Syntax_matchesNull(v___x_4052_, v___x_4053_);
if (v___x_4054_ == 0)
{
uint8_t v___x_4055_; 
v___x_4055_ = l_Lean_Syntax_matchesNull(v___x_4052_, v___x_4051_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_4039_);
v___x_4056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
else
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = l_Lean_Syntax_getArg(v_a_4039_, v___x_4065_);
lean_dec(v_a_4039_);
v___x_4067_ = l_Lean_Elab_Command_getRef___redArg(v_a_4033_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = l_Lean_SourceInfo_fromRef(v_a_4068_, v___x_4054_);
lean_dec(v_a_4068_);
v___x_4070_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4033_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v_a_4073_; lean_object* v_quotContext_x3f_4081_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v_quotContext_x3f_4081_ = lean_ctor_get(v_a_4033_, 5);
if (lean_obj_tag(v_quotContext_x3f_4081_) == 0)
{
lean_object* v___x_4082_; lean_object* v_a_4083_; 
v___x_4082_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_4034_);
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref(v___x_4082_);
v_a_4073_ = v_a_4083_;
goto v___jp_4072_;
}
else
{
lean_object* v_val_4084_; 
v_val_4084_ = lean_ctor_get(v_quotContext_x3f_4081_, 0);
lean_inc(v_val_4084_);
v_a_4073_ = v_val_4084_;
goto v___jp_4072_;
}
v___jp_4072_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4074_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_4075_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_4076_ = l_Lean_addMacroScope(v_a_4073_, v___x_4075_, v_a_4071_);
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4069_);
lean_ctor_set(v___x_4078_, 1, v___x_4074_);
lean_ctor_set(v___x_4078_, 2, v___x_4076_);
lean_ctor_set(v___x_4078_, 3, v___x_4077_);
v___x_4079_ = lean_box(0);
v___x_4080_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4079_, v___x_4078_, v___x_4066_, v_a_4033_, v_a_4034_);
return v___x_4080_;
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v___x_4069_);
lean_dec(v___x_4066_);
v_a_4085_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4070_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4070_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v___x_4066_);
v_a_4093_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4067_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4067_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
else
{
lean_object* v___x_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
v___x_4101_ = l_Lean_Syntax_getArg(v___x_4052_, v___x_4051_);
lean_dec(v___x_4052_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_4101_);
v___x_4103_ = l_Lean_Syntax_isOfKind(v___x_4101_, v___x_4102_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v___x_4101_);
lean_dec(v_a_4039_);
v___x_4104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4104_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4104_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4113_ = lean_unsigned_to_nat(1u);
v___x_4114_ = l_Lean_Syntax_getArg(v_a_4039_, v___x_4113_);
lean_dec(v_a_4039_);
lean_inc(v___x_4101_);
v___x_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4101_);
v___x_4116_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4115_, v___x_4101_, v___x_4114_, v_a_4033_, v_a_4034_);
return v___x_4116_;
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
v_a_4117_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4038_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4038_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_Elab_Command_expandMacroArg(v_stx_4125_, v_a_4126_, v_a_4127_);
lean_dec(v_a_4127_);
lean_dec_ref(v_a_4126_);
return v_res_4129_;
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
