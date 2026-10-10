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
uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_x_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(lean_object* v_00___17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
return v___x_18_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(lean_object* v_id_19_, lean_object* v___x_20_, uint8_t v___x_21_, uint8_t v___x_22_, lean_object* v_x_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = l_Lean_TSyntax_getId(v_id_19_);
v___x_28_ = l_Lean_Parser_getParserAliasInfo(v___x_27_);
lean_dec(v___x_27_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_44_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_44_ == 0)
{
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_44_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_44_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_stackSz_x3f_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_stackSz_x3f_33_ = lean_ctor_get(v_a_29_, 1);
lean_inc(v_stackSz_x3f_33_);
lean_dec(v_a_29_);
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_20_);
v___x_35_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_33_, v___x_34_);
lean_dec_ref_known(v___x_34_, 1);
lean_dec(v_stackSz_x3f_33_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_box(v___x_21_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_36_);
v___x_38_ = v___x_31_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = lean_box(v___x_22_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_40_);
v___x_42_ = v___x_31_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_57_; 
lean_dec(v___x_20_);
v_a_45_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_57_ == 0)
{
v___x_47_ = v___x_28_;
v_isShared_48_ = v_isSharedCheck_57_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_28_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_57_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_ref_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v_ref_49_ = lean_ctor_get(v___y_24_, 7);
v___x_50_ = lean_io_error_to_string(v_a_45_);
v___x_51_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
lean_inc(v_ref_49_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v_ref_49_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_53_);
v___x_55_ = v___x_47_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_19_ = stack[0].m_obj;
lean_object* v___x_20_ = stack[1].m_obj;
uint8_t v___x_21_ = stack[2].m_num;
uint8_t v___x_22_ = stack[3].m_num;
lean_object* v_x_23_ = stack[4].m_obj;
lean_object* v___y_24_ = stack[5].m_obj;
lean_object* v___y_25_ = stack[6].m_obj;
lean_object* v_res_58_;
v_res_58_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_19_, v___x_20_, v___x_21_, v___x_22_, v_x_23_, v___y_24_, v___y_25_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0___boxed(lean_object* v_id_59_, lean_object* v___x_60_, lean_object* v___x_61_, lean_object* v___x_62_, lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v___x_15315__boxed_67_; uint8_t v___x_15316__boxed_68_; lean_object* v_res_69_; 
v___x_15315__boxed_67_ = lean_unbox(v___x_61_);
v___x_15316__boxed_68_ = lean_unbox(v___x_62_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_59_, v___x_60_, v___x_15315__boxed_67_, v___x_15316__boxed_68_, v_x_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v_id_59_);
return v_res_69_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(uint8_t v___x_92_, lean_object* v_as_93_, size_t v_i_94_, size_t v_stop_95_, lean_object* v_b_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_a_101_; uint8_t v___x_105_; 
v___x_105_ = lean_usize_dec_eq(v_i_94_, v_stop_95_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v_a_113_; lean_object* v___y_115_; uint8_t v___x_126_; 
v___x_106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_array_uget_borrowed(v_as_93_, v_i_94_);
lean_inc(v___x_109_);
v___x_126_ = l_Lean_Syntax_isOfKind(v___x_109_, v___x_106_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_109_);
v___x_128_ = l_Lean_Syntax_isOfKind(v___x_109_, v___x_127_);
if (v___x_128_ == 0)
{
goto v___jp_110_;
}
else
{
lean_object* v_id_129_; 
v_id_129_ = l_Lean_Syntax_getArg(v___x_109_, v___x_107_);
if (v___x_126_ == 0)
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_129_);
v___x_154_ = l_Lean_Syntax_isOfKind(v_id_129_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_id_129_);
goto v___jp_110_;
}
else
{
goto v___jp_130_;
}
}
else
{
goto v___jp_130_;
}
v___jp_130_:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(2u);
v___x_132_ = l_Lean_Syntax_getArg(v___x_109_, v___x_131_);
v___x_133_ = l_Lean_Syntax_matchesNull(v___x_132_, v___x_108_);
if (v___x_133_ == 0)
{
lean_dec(v_id_129_);
goto v___jp_110_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = l_Lean_TSyntax_getId(v_id_129_);
lean_dec(v_id_129_);
v___x_135_ = l_Lean_Parser_getParserAliasInfo(v___x_134_);
lean_dec(v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_stackSz_x3f_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v_stackSz_x3f_137_ = lean_ctor_get(v_a_136_, 1);
lean_inc(v_stackSz_x3f_137_);
lean_dec(v_a_136_);
v___x_138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_139_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_137_, v___x_138_);
lean_dec(v_stackSz_x3f_137_);
if (v___x_139_ == 0)
{
v_a_113_ = v___x_133_;
goto v___jp_112_;
}
else
{
v_a_113_ = v___x_126_;
goto v___jp_112_;
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_b_96_);
v_a_140_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_152_ == 0)
{
v___x_142_ = v___x_135_;
v_isShared_143_ = v_isSharedCheck_152_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_135_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_152_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_ref_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v_ref_144_ = lean_ctor_get(v___y_97_, 7);
v___x_145_ = lean_io_error_to_string(v_a_140_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
v___x_147_ = l_Lean_MessageData_ofFormat(v___x_146_);
lean_inc(v_ref_144_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v_ref_144_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_148_);
v___x_150_ = v___x_142_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_155_; 
v_id_155_ = l_Lean_Syntax_getArg(v___x_109_, v___x_107_);
if (v___x_92_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_155_);
v___x_168_ = l_Lean_Syntax_isOfKind(v_id_155_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec(v_id_155_);
goto v___jp_110_;
}
else
{
goto v___jp_156_;
}
}
else
{
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = l_Lean_Syntax_getArg(v___x_109_, v___x_108_);
v___x_158_ = l_Lean_Syntax_isNone(v___x_157_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; 
lean_inc(v___x_157_);
v___x_159_ = l_Lean_Syntax_matchesNull(v___x_157_, v___x_108_);
if (v___x_159_ == 0)
{
lean_dec(v___x_157_);
lean_dec(v_id_155_);
goto v___jp_110_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Lean_Syntax_getArg(v___x_157_, v___x_107_);
lean_dec(v___x_157_);
v___x_161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_162_ = l_Lean_Syntax_isOfKind(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_dec(v_id_155_);
goto v___jp_110_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_155_, v___x_107_, v___x_126_, v___x_92_, v___x_163_, v___y_97_, v___y_98_);
lean_dec(v_id_155_);
v___y_115_ = v___x_164_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v___x_157_);
v___x_165_ = lean_box(0);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_155_, v___x_107_, v___x_126_, v___x_92_, v___x_165_, v___y_97_, v___y_98_);
lean_dec(v_id_155_);
v___y_115_ = v___x_166_;
goto v___jp_114_;
}
}
}
v___jp_110_:
{
lean_object* v___x_111_; 
lean_inc(v___x_109_);
v___x_111_ = lean_array_push(v_b_96_, v___x_109_);
v_a_101_ = v___x_111_;
goto v___jp_100_;
}
v___jp_112_:
{
if (v_a_113_ == 0)
{
v_a_101_ = v_b_96_;
goto v___jp_100_;
}
else
{
goto v___jp_110_;
}
}
v___jp_114_:
{
if (lean_obj_tag(v___y_115_) == 0)
{
lean_object* v_a_116_; uint8_t v___x_117_; 
v_a_116_ = lean_ctor_get(v___y_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___y_115_, 1);
v___x_117_ = lean_unbox(v_a_116_);
lean_dec(v_a_116_);
v_a_113_ = v___x_117_;
goto v___jp_112_;
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_b_96_);
v_a_118_ = lean_ctor_get(v___y_115_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___y_115_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___y_115_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___y_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_b_96_);
return v___x_169_;
}
v___jp_100_:
{
size_t v___x_102_; size_t v___x_103_; 
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_add(v_i_94_, v___x_102_);
v_i_94_ = v___x_103_;
v_b_96_ = v_a_101_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_92_ = stack[0].m_num;
lean_object* v_as_93_ = stack[1].m_obj;
size_t v_i_94_ = stack[2].m_num;
size_t v_stop_95_ = stack[3].m_num;
lean_object* v_b_96_ = stack[4].m_obj;
lean_object* v___y_97_ = stack[5].m_obj;
lean_object* v___y_98_ = stack[6].m_obj;
lean_object* v_res_170_;
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_92_, v_as_93_, v_i_94_, v_stop_95_, v_b_96_, v___y_97_, v___y_98_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object* v___x_171_, lean_object* v_as_172_, lean_object* v_i_173_, lean_object* v_stop_174_, lean_object* v_b_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v___x_15486__boxed_179_; size_t v_i_boxed_180_; size_t v_stop_boxed_181_; lean_object* v_res_182_; 
v___x_15486__boxed_179_ = lean_unbox(v___x_171_);
v_i_boxed_180_ = lean_unbox_usize(v_i_173_);
lean_dec(v_i_173_);
v_stop_boxed_181_ = lean_unbox_usize(v_stop_174_);
lean_dec(v_stop_174_);
v_res_182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_15486__boxed_179_, v_as_172_, v_i_boxed_180_, v_stop_boxed_181_, v_b_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec_ref(v_as_172_);
return v_res_182_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(uint8_t v___x_183_, lean_object* v_as_184_, size_t v_i_185_, size_t v_stop_186_, lean_object* v_b_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_a_192_; uint8_t v___x_196_; 
v___x_196_ = lean_usize_dec_eq(v_i_185_, v_stop_186_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v_a_204_; lean_object* v___y_206_; uint8_t v___x_217_; 
v___x_197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_array_uget_borrowed(v_as_184_, v_i_185_);
lean_inc(v___x_200_);
v___x_217_ = l_Lean_Syntax_isOfKind(v___x_200_, v___x_197_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_200_);
v___x_219_ = l_Lean_Syntax_isOfKind(v___x_200_, v___x_218_);
if (v___x_219_ == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v_id_220_; 
v_id_220_ = l_Lean_Syntax_getArg(v___x_200_, v___x_198_);
if (v___x_217_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_220_);
v___x_245_ = l_Lean_Syntax_isOfKind(v_id_220_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_id_220_);
goto v___jp_201_;
}
else
{
goto v___jp_221_;
}
}
else
{
goto v___jp_221_;
}
v___jp_221_:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = l_Lean_Syntax_getArg(v___x_200_, v___x_222_);
v___x_224_ = l_Lean_Syntax_matchesNull(v___x_223_, v___x_199_);
if (v___x_224_ == 0)
{
lean_dec(v_id_220_);
goto v___jp_201_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = l_Lean_TSyntax_getId(v_id_220_);
lean_dec(v_id_220_);
v___x_226_ = l_Lean_Parser_getParserAliasInfo(v___x_225_);
lean_dec(v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v_stackSz_x3f_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v_stackSz_x3f_228_ = lean_ctor_get(v_a_227_, 1);
lean_inc(v_stackSz_x3f_228_);
lean_dec(v_a_227_);
v___x_229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_230_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_228_, v___x_229_);
lean_dec(v_stackSz_x3f_228_);
if (v___x_230_ == 0)
{
v_a_204_ = v___x_224_;
goto v___jp_203_;
}
else
{
v_a_204_ = v___x_217_;
goto v___jp_203_;
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v_b_187_);
v_a_231_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_243_ == 0)
{
v___x_233_ = v___x_226_;
v_isShared_234_ = v_isSharedCheck_243_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_226_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_243_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_ref_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v_ref_235_ = lean_ctor_get(v___y_188_, 7);
v___x_236_ = lean_io_error_to_string(v_a_231_);
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = l_Lean_MessageData_ofFormat(v___x_237_);
lean_inc(v_ref_235_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_235_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_239_);
v___x_241_ = v___x_233_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_id_246_ = l_Lean_Syntax_getArg(v___x_200_, v___x_198_);
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_246_);
v___x_248_ = l_Lean_Syntax_isOfKind(v_id_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_id_246_);
goto v___jp_201_;
}
else
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = l_Lean_Syntax_getArg(v___x_200_, v___x_199_);
v___x_250_ = l_Lean_Syntax_isNone(v___x_249_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
lean_inc(v___x_249_);
v___x_251_ = l_Lean_Syntax_matchesNull(v___x_249_, v___x_199_);
if (v___x_251_ == 0)
{
lean_dec(v___x_249_);
lean_dec(v_id_246_);
goto v___jp_201_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = l_Lean_Syntax_getArg(v___x_249_, v___x_198_);
lean_dec(v___x_249_);
v___x_253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_254_ = l_Lean_Syntax_isOfKind(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_dec(v_id_246_);
goto v___jp_201_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_246_, v___x_198_, v___x_217_, v___x_183_, v___x_255_, v___y_188_, v___y_189_);
lean_dec(v_id_246_);
v___y_206_ = v___x_256_;
goto v___jp_205_;
}
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_249_);
v___x_257_ = lean_box(0);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_246_, v___x_198_, v___x_217_, v___x_183_, v___x_257_, v___y_188_, v___y_189_);
lean_dec(v_id_246_);
v___y_206_ = v___x_258_;
goto v___jp_205_;
}
}
}
v___jp_201_:
{
lean_object* v___x_202_; 
lean_inc(v___x_200_);
v___x_202_ = lean_array_push(v_b_187_, v___x_200_);
v_a_192_ = v___x_202_;
goto v___jp_191_;
}
v___jp_203_:
{
if (v_a_204_ == 0)
{
v_a_192_ = v_b_187_;
goto v___jp_191_;
}
else
{
goto v___jp_201_;
}
}
v___jp_205_:
{
if (lean_obj_tag(v___y_206_) == 0)
{
lean_object* v_a_207_; uint8_t v___x_208_; 
v_a_207_ = lean_ctor_get(v___y_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___y_206_, 1);
v___x_208_ = lean_unbox(v_a_207_);
lean_dec(v_a_207_);
v_a_204_ = v___x_208_;
goto v___jp_203_;
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_b_187_);
v_a_209_ = lean_ctor_get(v___y_206_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___y_206_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___y_206_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___y_206_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_b_187_);
return v___x_259_;
}
v___jp_191_:
{
size_t v___x_193_; size_t v___x_194_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_185_, v___x_193_);
v_i_185_ = v___x_194_;
v_b_187_ = v_a_192_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_183_ = stack[0].m_num;
lean_object* v_as_184_ = stack[1].m_obj;
size_t v_i_185_ = stack[2].m_num;
size_t v_stop_186_ = stack[3].m_num;
lean_object* v_b_187_ = stack[4].m_obj;
lean_object* v___y_188_ = stack[5].m_obj;
lean_object* v___y_189_ = stack[6].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_183_, v_as_184_, v_i_185_, v_stop_186_, v_b_187_, v___y_188_, v___y_189_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object* v___x_261_, lean_object* v_as_262_, lean_object* v_i_263_, lean_object* v_stop_264_, lean_object* v_b_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
uint8_t v___x_15776__boxed_269_; size_t v_i_boxed_270_; size_t v_stop_boxed_271_; lean_object* v_res_272_; 
v___x_15776__boxed_269_ = lean_unbox(v___x_261_);
v_i_boxed_270_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_stop_boxed_271_ = lean_unbox_usize(v_stop_264_);
lean_dec(v_stop_264_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_15776__boxed_269_, v_as_262_, v_i_boxed_270_, v_stop_boxed_271_, v_b_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec_ref(v_as_262_);
return v_res_272_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(uint8_t v___x_273_, lean_object* v_as_274_, size_t v_i_275_, size_t v_stop_276_, lean_object* v_b_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_a_282_; uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_eq(v_i_275_, v_stop_276_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v_a_294_; lean_object* v___y_296_; uint8_t v___x_307_; 
v___x_287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_array_uget_borrowed(v_as_274_, v_i_275_);
lean_inc(v___x_290_);
v___x_307_ = l_Lean_Syntax_isOfKind(v___x_290_, v___x_287_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_290_);
v___x_309_ = l_Lean_Syntax_isOfKind(v___x_290_, v___x_308_);
if (v___x_309_ == 0)
{
goto v___jp_291_;
}
else
{
lean_object* v_id_310_; 
v_id_310_ = l_Lean_Syntax_getArg(v___x_290_, v___x_288_);
if (v___x_307_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_310_);
v___x_335_ = l_Lean_Syntax_isOfKind(v_id_310_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_id_310_);
goto v___jp_291_;
}
else
{
goto v___jp_311_;
}
}
else
{
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_unsigned_to_nat(2u);
v___x_313_ = l_Lean_Syntax_getArg(v___x_290_, v___x_312_);
v___x_314_ = l_Lean_Syntax_matchesNull(v___x_313_, v___x_289_);
if (v___x_314_ == 0)
{
lean_dec(v_id_310_);
goto v___jp_291_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = l_Lean_TSyntax_getId(v_id_310_);
lean_dec(v_id_310_);
v___x_316_ = l_Lean_Parser_getParserAliasInfo(v___x_315_);
lean_dec(v___x_315_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v_stackSz_x3f_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v_stackSz_x3f_318_ = lean_ctor_get(v_a_317_, 1);
lean_inc(v_stackSz_x3f_318_);
lean_dec(v_a_317_);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_320_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_318_, v___x_319_);
lean_dec(v_stackSz_x3f_318_);
if (v___x_320_ == 0)
{
v_a_294_ = v___x_314_;
goto v___jp_293_;
}
else
{
v_a_294_ = v___x_307_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_b_277_);
v_a_321_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_333_ == 0)
{
v___x_323_ = v___x_316_;
v_isShared_324_ = v_isSharedCheck_333_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_333_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_ref_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v_ref_325_ = lean_ctor_get(v___y_278_, 7);
v___x_326_ = lean_io_error_to_string(v_a_321_);
v___x_327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = l_Lean_MessageData_ofFormat(v___x_327_);
lean_inc(v_ref_325_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_ref_325_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_329_);
v___x_331_ = v___x_323_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v_id_337_; 
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v_id_337_ = l_Lean_Syntax_getArg(v___x_290_, v___x_288_);
if (v___x_273_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_337_);
v___x_349_ = l_Lean_Syntax_isOfKind(v_id_337_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec(v_id_337_);
goto v___jp_291_;
}
else
{
goto v___jp_338_;
}
}
else
{
goto v___jp_338_;
}
v___jp_338_:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = l_Lean_Syntax_getArg(v___x_290_, v___x_289_);
v___x_340_ = l_Lean_Syntax_isNone(v___x_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
lean_inc(v___x_339_);
v___x_341_ = l_Lean_Syntax_matchesNull(v___x_339_, v___x_289_);
if (v___x_341_ == 0)
{
lean_dec(v___x_339_);
lean_dec(v_id_337_);
goto v___jp_291_;
}
else
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = l_Lean_Syntax_getArg(v___x_339_, v___x_288_);
lean_dec(v___x_339_);
v___x_343_ = l_Lean_Syntax_isOfKind(v___x_342_, v___x_336_);
if (v___x_343_ == 0)
{
lean_dec(v_id_337_);
goto v___jp_291_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box(0);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_337_, v___x_288_, v___x_307_, v___x_273_, v___x_344_, v___y_278_, v___y_279_);
lean_dec(v_id_337_);
v___y_296_ = v___x_345_;
goto v___jp_295_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v___x_339_);
v___x_346_ = lean_box(0);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_337_, v___x_288_, v___x_307_, v___x_273_, v___x_346_, v___y_278_, v___y_279_);
lean_dec(v_id_337_);
v___y_296_ = v___x_347_;
goto v___jp_295_;
}
}
}
v___jp_291_:
{
lean_object* v___x_292_; 
lean_inc(v___x_290_);
v___x_292_ = lean_array_push(v_b_277_, v___x_290_);
v_a_282_ = v___x_292_;
goto v___jp_281_;
}
v___jp_293_:
{
if (v_a_294_ == 0)
{
v_a_282_ = v_b_277_;
goto v___jp_281_;
}
else
{
goto v___jp_291_;
}
}
v___jp_295_:
{
if (lean_obj_tag(v___y_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___y_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___y_296_, 1);
v___x_298_ = lean_unbox(v_a_297_);
lean_dec(v_a_297_);
v_a_294_ = v___x_298_;
goto v___jp_293_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_b_277_);
v_a_299_ = lean_ctor_get(v___y_296_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___y_296_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___y_296_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___y_296_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v_b_277_);
return v___x_350_;
}
v___jp_281_:
{
size_t v___x_283_; size_t v___x_284_; 
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_275_, v___x_283_);
v_i_275_ = v___x_284_;
v_b_277_ = v_a_282_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_273_ = stack[0].m_num;
lean_object* v_as_274_ = stack[1].m_obj;
size_t v_i_275_ = stack[2].m_num;
size_t v_stop_276_ = stack[3].m_num;
lean_object* v_b_277_ = stack[4].m_obj;
lean_object* v___y_278_ = stack[5].m_obj;
lean_object* v___y_279_ = stack[6].m_obj;
lean_object* v_res_351_;
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_273_, v_as_274_, v_i_275_, v_stop_276_, v_b_277_, v___y_278_, v___y_279_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5___boxed(lean_object* v___x_352_, lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_stop_355_, lean_object* v_b_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v___x_16027__boxed_360_; size_t v_i_boxed_361_; size_t v_stop_boxed_362_; lean_object* v_res_363_; 
v___x_16027__boxed_360_ = lean_unbox(v___x_352_);
v_i_boxed_361_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_stop_boxed_362_ = lean_unbox_usize(v_stop_355_);
lean_dec(v_stop_355_);
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_16027__boxed_360_, v_as_353_, v_i_boxed_361_, v_stop_boxed_362_, v_b_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_as_353_);
return v_res_363_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(lean_object* v_opts_364_, lean_object* v_opt_365_){
_start:
{
lean_object* v_name_366_; lean_object* v_defValue_367_; lean_object* v_map_368_; lean_object* v___x_369_; 
v_name_366_ = lean_ctor_get(v_opt_365_, 0);
v_defValue_367_ = lean_ctor_get(v_opt_365_, 1);
v_map_368_ = lean_ctor_get(v_opts_364_, 0);
v___x_369_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_368_, v_name_366_);
if (lean_obj_tag(v___x_369_) == 0)
{
uint8_t v___x_370_; 
v___x_370_ = lean_unbox(v_defValue_367_);
return v___x_370_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_369_, 1);
if (lean_obj_tag(v_val_371_) == 1)
{
uint8_t v_v_372_; 
v_v_372_ = lean_ctor_get_uint8(v_val_371_, 0);
lean_dec_ref_known(v_val_371_, 0);
return v_v_372_;
}
else
{
uint8_t v___x_373_; 
lean_dec(v_val_371_);
v___x_373_ = lean_unbox(v_defValue_367_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_364_ = stack[0].m_obj;
lean_object* v_opt_365_ = stack[1].m_obj;
uint8_t v_res_374_;
v_res_374_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_364_, v_opt_365_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_375_, lean_object* v_opt_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_375_, v_opt_376_);
lean_dec_ref(v_opt_376_);
lean_dec_ref(v_opts_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_box(1);
v___x_380_ = l_Lean_MessageData_ofFormat(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2));
v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
return v_x_386_;
}
else
{
lean_object* v_head_388_; lean_object* v_tail_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_411_; 
v_head_388_ = lean_ctor_get(v_x_387_, 0);
v_tail_389_ = lean_ctor_get(v_x_387_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_411_ == 0)
{
v___x_391_ = v_x_387_;
v_isShared_392_ = v_isSharedCheck_411_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_tail_389_);
lean_inc(v_head_388_);
lean_dec(v_x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_411_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_before_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_409_; 
v_before_393_ = lean_ctor_get(v_head_388_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_head_388_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v_head_388_, 1);
lean_dec(v_unused_410_);
v___x_395_ = v_head_388_;
v_isShared_396_ = v_isSharedCheck_409_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_before_393_);
lean_dec(v_head_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_409_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 7);
lean_ctor_set(v___x_395_, 1, v___x_397_);
lean_ctor_set(v___x_395_, 0, v_x_386_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_x_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_408_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 7);
lean_ctor_set(v___x_391_, 1, v___x_400_);
lean_ctor_set(v___x_391_, 0, v___x_399_);
v___x_402_ = v___x_391_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_400_);
v___x_402_ = v_reuseFailAlloc_407_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = l_Lean_MessageData_ofSyntax(v_before_393_);
v___x_404_ = l_Lean_indentD(v___x_403_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v_x_386_ = v___x_405_;
v_x_387_ = v_tail_389_;
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
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1));
v___x_416_ = l_Lean_MessageData_ofFormat(v___x_415_);
return v___x_416_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(lean_object* v_msgData_417_, lean_object* v_macroStack_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_scopes_423_; lean_object* v___x_424_; lean_object* v_opts_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_421_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_422_ = lean_st_ref_get(v___y_419_);
v_scopes_423_ = lean_ctor_get(v___x_422_, 2);
lean_inc(v_scopes_423_);
lean_dec(v___x_422_);
v___x_424_ = l_List_head_x21___redArg(v___x_421_, v_scopes_423_);
lean_dec(v_scopes_423_);
v_opts_425_ = lean_ctor_get(v___x_424_, 1);
lean_inc_ref(v_opts_425_);
lean_dec(v___x_424_);
v___x_426_ = l_Lean_Elab_pp_macroStack;
v___x_427_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_425_, v___x_426_);
lean_dec_ref(v_opts_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_macroStack_418_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_msgData_417_);
return v___x_428_;
}
else
{
if (lean_obj_tag(v_macroStack_418_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_msgData_417_);
return v___x_429_;
}
else
{
lean_object* v_head_430_; lean_object* v_after_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_446_; 
v_head_430_ = lean_ctor_get(v_macroStack_418_, 0);
lean_inc(v_head_430_);
v_after_431_ = lean_ctor_get(v_head_430_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_head_430_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_head_430_, 0);
lean_dec(v_unused_447_);
v___x_433_ = v_head_430_;
v_isShared_434_ = v_isSharedCheck_446_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_after_431_);
lean_dec(v_head_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_446_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 7);
lean_ctor_set(v___x_433_, 1, v___x_435_);
lean_ctor_set(v___x_433_, 0, v_msgData_417_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_msgData_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_445_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_msgData_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_438_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_MessageData_ofSyntax(v_after_431_);
v___x_441_ = l_Lean_indentD(v___x_440_);
v_msgData_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_442_, 0, v___x_439_);
lean_ctor_set(v_msgData_442_, 1, v___x_441_);
v___x_443_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(v_msgData_442_, v_macroStack_418_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_417_ = stack[0].m_obj;
lean_object* v_macroStack_418_ = stack[1].m_obj;
lean_object* v___y_419_ = stack[2].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_417_, v_macroStack_418_, v___y_419_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_449_, lean_object* v_macroStack_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_449_, v_macroStack_450_, v___y_451_);
lean_dec(v___y_451_);
return v_res_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_454_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_458_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
lean_ctor_set(v___x_460_, 4, v___x_458_);
lean_ctor_set(v___x_460_, 5, v___x_458_);
lean_ctor_set(v___x_460_, 6, v___x_458_);
lean_ctor_set(v___x_460_, 7, v___x_458_);
lean_ctor_set(v___x_460_, 8, v___x_458_);
lean_ctor_set(v___x_460_, 9, v___x_458_);
lean_ctor_set(v___x_460_, 10, v___x_458_);
lean_ctor_set(v___x_460_, 11, v___x_457_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(32u);
v___x_462_ = lean_mk_empty_array_with_capacity(v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_464_ = ((size_t)5ULL);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_unsigned_to_nat(32u);
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_466_);
v___x_468_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_469_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
lean_ctor_set(v___x_469_, 2, v___x_465_);
lean_ctor_set(v___x_469_, 3, v___x_465_);
lean_ctor_set_usize(v___x_469_, 4, v___x_464_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = lean_box(1);
v___x_471_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_472_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
lean_ctor_set(v___x_473_, 2, v___x_470_);
return v___x_473_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_env_478_; uint8_t v___x_479_; lean_object* v_env_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_scopes_483_; lean_object* v___x_484_; lean_object* v_opts_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_477_ = lean_st_ref_get(v___y_475_);
v_env_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_env_478_);
lean_dec(v___x_477_);
v___x_479_ = 0;
v_env_480_ = l_Lean_Environment_setRecordingDeps(v_env_478_, v___x_479_);
v___x_481_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_482_ = lean_st_ref_get(v___y_475_);
v_scopes_483_ = lean_ctor_get(v___x_482_, 2);
lean_inc(v_scopes_483_);
lean_dec(v___x_482_);
v___x_484_ = l_List_head_x21___redArg(v___x_481_, v_scopes_483_);
lean_dec(v_scopes_483_);
v_opts_485_ = lean_ctor_get(v___x_484_, 1);
lean_inc_ref(v_opts_485_);
lean_dec(v___x_484_);
v___x_486_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_487_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_488_, 0, v_env_480_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
lean_ctor_set(v___x_488_, 3, v_opts_485_);
v___x_489_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_msgData_474_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_474_ = stack[0].m_obj;
lean_object* v___y_475_ = stack[1].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_474_, v___y_475_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_492_, v___y_493_);
lean_dec(v___y_493_);
return v_res_495_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Elab_Command_getRef___redArg(v___y_497_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_macroStack_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___x_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_macroStack_502_ = lean_ctor_get(v___y_497_, 4);
v___x_503_ = l_Lean_Elab_getBetterRef(v_a_501_, v_macroStack_502_);
lean_dec(v_a_501_);
v___x_504_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_496_, v___y_498_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
lean_inc(v_macroStack_502_);
v___x_506_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_505_, v_macroStack_502_, v___y_498_);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_503_);
lean_ctor_set(v___x_511_, 1, v_a_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v_msg_496_);
v_a_516_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_500_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_500_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_496_ = stack[0].m_obj;
lean_object* v___y_497_ = stack[1].m_obj;
lean_object* v___y_498_ = stack[2].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_496_, v___y_497_, v___y_498_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_529_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t v___x_530_, lean_object* v_as_531_, size_t v_i_532_, size_t v_stop_533_, lean_object* v_b_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_a_539_; uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_eq(v_i_532_, v_stop_533_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v_a_549_; lean_object* v___y_551_; uint8_t v___x_562_; 
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_545_ = lean_array_uget_borrowed(v_as_531_, v_i_532_);
lean_inc(v___x_545_);
v___x_562_ = l_Lean_Syntax_isOfKind(v___x_545_, v___x_544_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_545_);
v___x_564_ = l_Lean_Syntax_isOfKind(v___x_545_, v___x_563_);
if (v___x_564_ == 0)
{
goto v___jp_546_;
}
else
{
lean_object* v___x_565_; lean_object* v_id_566_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v_id_566_ = l_Lean_Syntax_getArg(v___x_545_, v___x_565_);
if (v___x_562_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_566_);
v___x_592_ = l_Lean_Syntax_isOfKind(v_id_566_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_id_566_);
goto v___jp_546_;
}
else
{
goto v___jp_567_;
}
}
else
{
goto v___jp_567_;
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_unsigned_to_nat(2u);
v___x_570_ = l_Lean_Syntax_getArg(v___x_545_, v___x_569_);
v___x_571_ = l_Lean_Syntax_matchesNull(v___x_570_, v___x_568_);
if (v___x_571_ == 0)
{
lean_dec(v_id_566_);
goto v___jp_546_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Lean_TSyntax_getId(v_id_566_);
lean_dec(v_id_566_);
v___x_573_ = l_Lean_Parser_getParserAliasInfo(v___x_572_);
lean_dec(v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_stackSz_x3f_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v_stackSz_x3f_575_ = lean_ctor_get(v_a_574_, 1);
lean_inc(v_stackSz_x3f_575_);
lean_dec(v_a_574_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_577_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_575_, v___x_576_);
lean_dec(v_stackSz_x3f_575_);
if (v___x_577_ == 0)
{
v_a_549_ = v___x_571_;
goto v___jp_548_;
}
else
{
v_a_549_ = v___x_562_;
goto v___jp_548_;
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_b_534_);
v_a_578_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_590_ == 0)
{
v___x_580_ = v___x_573_;
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_573_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_ref_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v_ref_582_ = lean_ctor_get(v___y_535_, 7);
v___x_583_ = lean_io_error_to_string(v_a_578_);
v___x_584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
v___x_585_ = l_Lean_MessageData_ofFormat(v___x_584_);
lean_inc(v_ref_582_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_ref_582_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_586_);
v___x_588_ = v___x_580_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_593_; lean_object* v_id_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v_id_594_ = l_Lean_Syntax_getArg(v___x_545_, v___x_593_);
if (v___x_530_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_594_);
v___x_608_ = l_Lean_Syntax_isOfKind(v_id_594_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_id_594_);
goto v___jp_546_;
}
else
{
goto v___jp_595_;
}
}
else
{
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = l_Lean_Syntax_getArg(v___x_545_, v___x_596_);
v___x_598_ = l_Lean_Syntax_isNone(v___x_597_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
lean_inc(v___x_597_);
v___x_599_ = l_Lean_Syntax_matchesNull(v___x_597_, v___x_596_);
if (v___x_599_ == 0)
{
lean_dec(v___x_597_);
lean_dec(v_id_594_);
goto v___jp_546_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = l_Lean_Syntax_getArg(v___x_597_, v___x_593_);
lean_dec(v___x_597_);
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_602_ = l_Lean_Syntax_isOfKind(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_id_594_);
goto v___jp_546_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_594_, v___x_593_, v___x_562_, v___x_530_, v___x_603_, v___y_535_, v___y_536_);
lean_dec(v_id_594_);
v___y_551_ = v___x_604_;
goto v___jp_550_;
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v___x_597_);
v___x_605_ = lean_box(0);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_594_, v___x_593_, v___x_562_, v___x_530_, v___x_605_, v___y_535_, v___y_536_);
lean_dec(v_id_594_);
v___y_551_ = v___x_606_;
goto v___jp_550_;
}
}
}
v___jp_546_:
{
lean_object* v___x_547_; 
lean_inc(v___x_545_);
v___x_547_ = lean_array_push(v_b_534_, v___x_545_);
v_a_539_ = v___x_547_;
goto v___jp_538_;
}
v___jp_548_:
{
if (v_a_549_ == 0)
{
v_a_539_ = v_b_534_;
goto v___jp_538_;
}
else
{
goto v___jp_546_;
}
}
v___jp_550_:
{
if (lean_obj_tag(v___y_551_) == 0)
{
lean_object* v_a_552_; uint8_t v___x_553_; 
v_a_552_ = lean_ctor_get(v___y_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___y_551_, 1);
v___x_553_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
v_a_549_ = v___x_553_;
goto v___jp_548_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_b_534_);
v_a_554_ = lean_ctor_get(v___y_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___y_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___y_551_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___y_551_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_b_534_);
return v___x_609_;
}
v___jp_538_:
{
size_t v___x_540_; size_t v___x_541_; 
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_add(v_i_532_, v___x_540_);
v_i_532_ = v___x_541_;
v_b_534_ = v_a_539_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_530_ = stack[0].m_num;
lean_object* v_as_531_ = stack[1].m_obj;
size_t v_i_532_ = stack[2].m_num;
size_t v_stop_533_ = stack[3].m_num;
lean_object* v_b_534_ = stack[4].m_obj;
lean_object* v___y_535_ = stack[5].m_obj;
lean_object* v___y_536_ = stack[6].m_obj;
lean_object* v_res_610_;
v_res_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_530_, v_as_531_, v_i_532_, v_stop_533_, v_b_534_, v___y_535_, v___y_536_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v___x_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_, lean_object* v_b_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
uint8_t v___x_16726__boxed_619_; size_t v_i_boxed_620_; size_t v_stop_boxed_621_; lean_object* v_res_622_; 
v___x_16726__boxed_619_ = lean_unbox(v___x_611_);
v_i_boxed_620_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_621_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_16726__boxed_619_, v_as_612_, v_i_boxed_620_, v_stop_boxed_621_, v_b_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_as_612_);
return v_res_622_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(0);
v___x_636_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; uint8_t v___x_653_; 
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_644_);
v___x_652_ = l_Lean_Syntax_isOfKind(v_a_644_, v___x_651_);
v___x_653_ = 1;
if (v___x_652_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_644_);
v___x_661_ = l_Lean_Syntax_isOfKind(v_a_644_, v___x_660_);
if (v___x_661_ == 0)
{
lean_dec(v_a_644_);
goto v___jp_654_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_a_667_; lean_object* v___y_673_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = l_Lean_Syntax_getArg(v_a_644_, v___x_662_);
lean_dec(v_a_644_);
v___x_664_ = l_Lean_Syntax_getArgs(v___x_663_);
lean_dec(v___x_663_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_size(v___x_664_);
v___x_684_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_685_ = lean_nat_dec_lt(v___x_665_, v___x_683_);
if (v___x_685_ == 0)
{
lean_dec_ref(v___x_664_);
v_a_667_ = v___x_684_;
goto v___jp_666_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = lean_nat_dec_le(v___x_683_, v___x_683_);
if (v___x_686_ == 0)
{
if (v___x_685_ == 0)
{
lean_dec_ref(v___x_664_);
v_a_667_ = v___x_684_;
goto v___jp_666_;
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_683_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_652_, v___x_664_, v___x_687_, v___x_688_, v___x_684_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_664_);
v___y_673_ = v___x_689_;
goto v___jp_672_;
}
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_683_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_652_, v___x_664_, v___x_690_, v___x_691_, v___x_684_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_664_);
v___y_673_ = v___x_692_;
goto v___jp_672_;
}
}
v___jp_666_:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_a_667_);
v___x_669_ = lean_nat_dec_eq(v___x_668_, v___x_662_);
if (v___x_669_ == 0)
{
lean_dec_ref(v_a_667_);
goto v___jp_654_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_array_fget(v_a_667_, v___x_665_);
lean_dec_ref(v_a_667_);
v_a_644_ = v___x_670_;
goto _start;
}
}
v___jp_672_:
{
if (lean_obj_tag(v___y_673_) == 0)
{
lean_object* v_a_674_; 
v_a_674_ = lean_ctor_get(v___y_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___y_673_, 1);
v_a_667_ = v_a_674_;
goto v___jp_666_;
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_a_645_);
v_a_675_ = lean_ctor_get(v___y_673_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___y_673_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___y_673_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___y_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
else
{
lean_object* v___x_693_; lean_object* v___y_705_; lean_object* v___y_711_; lean_object* v_id_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v_id_721_ = l_Lean_Syntax_getArg(v_a_644_, v___x_693_);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_721_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_id_721_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; uint8_t v___x_726_; 
lean_dec(v_id_721_);
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_644_);
v___x_726_ = l_Lean_Syntax_isOfKind(v_a_644_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v_a_644_);
goto v___jp_716_;
}
else
{
lean_object* v___x_727_; lean_object* v_a_729_; lean_object* v___y_735_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_745_ = l_Lean_Syntax_getArg(v_a_644_, v___x_727_);
lean_dec(v_a_644_);
v___x_746_ = l_Lean_Syntax_getArgs(v___x_745_);
lean_dec(v___x_745_);
v___x_747_ = lean_array_get_size(v___x_746_);
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_749_ = lean_nat_dec_lt(v___x_693_, v___x_747_);
if (v___x_749_ == 0)
{
lean_dec_ref(v___x_746_);
v_a_729_ = v___x_748_;
goto v___jp_728_;
}
else
{
uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_le(v___x_747_, v___x_747_);
if (v___x_750_ == 0)
{
if (v___x_749_ == 0)
{
lean_dec_ref(v___x_746_);
v_a_729_ = v___x_748_;
goto v___jp_728_;
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_747_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_724_, v___x_746_, v___x_751_, v___x_752_, v___x_748_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_746_);
v___y_735_ = v___x_753_;
goto v___jp_734_;
}
}
else
{
size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_747_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_724_, v___x_746_, v___x_754_, v___x_755_, v___x_748_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_746_);
v___y_735_ = v___x_756_;
goto v___jp_734_;
}
}
v___jp_728_:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_a_729_);
v___x_731_ = lean_nat_dec_eq(v___x_730_, v___x_727_);
if (v___x_731_ == 0)
{
lean_dec_ref(v_a_729_);
goto v___jp_716_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_array_fget(v_a_729_, v___x_693_);
lean_dec_ref(v_a_729_);
v_a_644_ = v___x_732_;
goto _start;
}
}
v___jp_734_:
{
if (lean_obj_tag(v___y_735_) == 0)
{
lean_object* v_a_736_; 
v_a_736_ = lean_ctor_get(v___y_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___y_735_, 1);
v_a_729_ = v_a_736_;
goto v___jp_728_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_a_645_);
v_a_737_ = lean_ctor_get(v___y_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___y_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___y_735_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___y_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
else
{
lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___x_839_; lean_object* v_a_841_; lean_object* v___y_847_; lean_object* v_a_858_; lean_object* v___y_864_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_874_ = l_Lean_Syntax_getArg(v_a_644_, v___x_839_);
v___x_875_ = l_Lean_Syntax_isNone(v___x_874_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; 
lean_inc(v___x_874_);
v___x_876_ = l_Lean_Syntax_matchesNull(v___x_874_, v___x_839_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; uint8_t v___x_878_; 
lean_dec(v_id_721_);
v___x_877_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_878_ = l_Lean_Syntax_isOfKind(v_a_644_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec(v___x_874_);
goto v___jp_699_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_879_ = l_Lean_Syntax_getArgs(v___x_874_);
lean_dec(v___x_874_);
v___x_880_ = lean_array_get_size(v___x_879_);
v___x_881_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_882_ = lean_nat_dec_lt(v___x_693_, v___x_880_);
if (v___x_882_ == 0)
{
lean_dec_ref(v___x_879_);
v_a_858_ = v___x_881_;
goto v___jp_857_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = lean_nat_dec_le(v___x_880_, v___x_880_);
if (v___x_883_ == 0)
{
if (v___x_882_ == 0)
{
lean_dec_ref(v___x_879_);
v_a_858_ = v___x_881_;
goto v___jp_857_;
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_880_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_876_, v___x_879_, v___x_884_, v___x_885_, v___x_881_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_879_);
v___y_864_ = v___x_886_;
goto v___jp_863_;
}
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_of_nat(v___x_880_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_876_, v___x_879_, v___x_887_, v___x_888_, v___x_881_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_879_);
v___y_864_ = v___x_889_;
goto v___jp_863_;
}
}
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = l_Lean_Syntax_getArg(v___x_874_, v___x_693_);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_892_ = l_Lean_Syntax_isOfKind(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; uint8_t v___x_894_; 
lean_dec(v_id_721_);
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_894_ = l_Lean_Syntax_isOfKind(v_a_644_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec(v___x_874_);
goto v___jp_694_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_895_ = l_Lean_Syntax_getArgs(v___x_874_);
lean_dec(v___x_874_);
v___x_896_ = lean_array_get_size(v___x_895_);
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_898_ = lean_nat_dec_lt(v___x_693_, v___x_896_);
if (v___x_898_ == 0)
{
lean_dec_ref(v___x_895_);
v_a_841_ = v___x_897_;
goto v___jp_840_;
}
else
{
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_le(v___x_896_, v___x_896_);
if (v___x_899_ == 0)
{
if (v___x_898_ == 0)
{
lean_dec_ref(v___x_895_);
v_a_841_ = v___x_897_;
goto v___jp_840_;
}
else
{
size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((size_t)0ULL);
v___x_901_ = lean_usize_of_nat(v___x_896_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_892_, v___x_895_, v___x_900_, v___x_901_, v___x_897_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_895_);
v___y_847_ = v___x_902_;
goto v___jp_846_;
}
}
else
{
size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((size_t)0ULL);
v___x_904_ = lean_usize_of_nat(v___x_896_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__5(v___x_892_, v___x_895_, v___x_903_, v___x_904_, v___x_897_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_895_);
v___y_847_ = v___x_905_;
goto v___jp_846_;
}
}
}
}
else
{
lean_dec(v___x_874_);
lean_dec(v_a_644_);
v___y_758_ = v_a_646_;
v___y_759_ = v_a_647_;
goto v___jp_757_;
}
}
}
else
{
lean_dec(v___x_874_);
lean_dec(v_a_644_);
v___y_758_ = v_a_646_;
v___y_759_ = v_a_647_;
goto v___jp_757_;
}
v___jp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_inc(v_id_721_);
v___x_760_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_760_, 0, v_id_721_);
v___x_761_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_760_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_830_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_830_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_830_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_830_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
if (lean_obj_tag(v_a_762_) == 1)
{
lean_object* v_val_766_; 
v_val_766_ = lean_ctor_get(v_a_762_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_a_762_, 1);
switch(lean_obj_tag(v_val_766_))
{
case 0:
{
lean_object* v_cat_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_id_721_);
v_cat_767_ = lean_ctor_get(v_val_766_, 0);
lean_inc(v_cat_767_);
lean_dec_ref_known(v_val_766_, 1);
v___x_768_ = lean_box(0);
v___x_769_ = l_Lean_Syntax_mkAntiquotNode(v_cat_767_, v_a_645_, v___x_693_, v___x_768_, v___x_653_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_769_);
v___x_771_ = v___x_764_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
case 1:
{
lean_object* v_decl_773_; 
lean_del_object(v___x_764_);
lean_dec(v_id_721_);
v_decl_773_ = lean_ctor_get(v_val_766_, 0);
lean_inc(v_decl_773_);
lean_dec_ref_known(v_val_766_, 1);
if (lean_obj_tag(v_decl_773_) == 1)
{
lean_object* v_pre_774_; 
v_pre_774_ = lean_ctor_get(v_decl_773_, 0);
if (lean_obj_tag(v_pre_774_) == 1)
{
lean_object* v_pre_775_; 
v_pre_775_ = lean_ctor_get(v_pre_774_, 0);
if (lean_obj_tag(v_pre_775_) == 1)
{
lean_object* v_pre_776_; 
v_pre_776_ = lean_ctor_get(v_pre_775_, 0);
switch(lean_obj_tag(v_pre_776_))
{
case 0:
{
lean_object* v_str_777_; lean_object* v_str_778_; lean_object* v_str_779_; uint8_t v___x_780_; 
v_str_777_ = lean_ctor_get(v_decl_773_, 1);
v_str_778_ = lean_ctor_get(v_pre_774_, 1);
v_str_779_ = lean_ctor_get(v_pre_775_, 1);
v___x_780_ = lean_string_dec_eq(v_str_779_, v___x_649_);
if (v___x_780_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = lean_string_dec_eq(v_str_778_, v___x_650_);
if (v___x_781_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = lean_string_dec_eq(v_str_777_, v___x_722_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_784_ = lean_string_dec_eq(v_str_777_, v___x_783_);
if (v___x_784_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
lean_object* v___x_785_; 
lean_dec_ref_known(v_decl_773_, 2);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_705_ = v___x_785_;
goto v___jp_704_;
}
}
else
{
lean_object* v___x_786_; 
lean_dec_ref_known(v_decl_773_, 2);
v___x_786_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_705_ = v___x_786_;
goto v___jp_704_;
}
}
}
}
case 1:
{
lean_object* v_pre_787_; 
v_pre_787_ = lean_ctor_get(v_pre_776_, 0);
if (lean_obj_tag(v_pre_787_) == 0)
{
lean_object* v_str_788_; lean_object* v_str_789_; lean_object* v_str_790_; lean_object* v_str_791_; uint8_t v___x_792_; 
v_str_788_ = lean_ctor_get(v_decl_773_, 1);
v_str_789_ = lean_ctor_get(v_pre_774_, 1);
v_str_790_ = lean_ctor_get(v_pre_775_, 1);
v_str_791_ = lean_ctor_get(v_pre_776_, 1);
v___x_792_ = lean_string_dec_eq(v_str_791_, v___x_649_);
if (v___x_792_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = lean_string_dec_eq(v_str_790_, v___x_650_);
if (v___x_793_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_795_ = lean_string_dec_eq(v_str_789_, v___x_794_);
if (v___x_795_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = lean_string_dec_eq(v_str_788_, v___x_722_);
if (v___x_796_ == 0)
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
else
{
lean_object* v___x_797_; 
lean_dec_ref_known(v_decl_773_, 2);
v___x_797_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_705_ = v___x_797_;
goto v___jp_704_;
}
}
}
}
}
else
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
}
default: 
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
}
}
else
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
}
else
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
}
else
{
v___y_705_ = v_decl_773_;
goto v___jp_704_;
}
}
default: 
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_764_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_val_766_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_val_766_, 0);
lean_dec(v_unused_823_);
v___x_799_ = v_val_766_;
v_isShared_800_ = v_isSharedCheck_822_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_val_766_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_822_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = l_Lean_TSyntax_getId(v_id_721_);
lean_dec(v_id_721_);
v___x_802_ = l_Lean_Name_eraseMacroScopes(v___x_801_);
lean_dec(v___x_801_);
v___x_803_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_802_);
lean_dec(v___x_802_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
lean_del_object(v___x_799_);
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
if (lean_obj_tag(v_a_804_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_box(0);
v___y_711_ = v___x_805_;
goto v___jp_710_;
}
else
{
lean_object* v_val_806_; 
v_val_806_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_a_804_, 1);
v___y_711_ = v_val_806_;
goto v___jp_710_;
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_a_645_);
v_a_807_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_821_ == 0)
{
v___x_809_ = v___x_803_;
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_803_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_ref_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v_ref_811_ = lean_ctor_get(v___y_758_, 7);
v___x_812_ = lean_io_error_to_string(v_a_807_);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 3);
lean_ctor_set(v___x_799_, 0, v___x_812_);
v___x_814_ = v___x_799_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_820_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = l_Lean_MessageData_ofFormat(v___x_814_);
lean_inc(v_ref_811_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_ref_811_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
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
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_764_);
lean_dec(v_a_762_);
lean_dec(v_a_645_);
v___x_824_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_825_ = l_Lean_MessageData_ofSyntax(v_id_721_);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_828_, v___y_758_, v___y_759_);
return v___x_829_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_id_721_);
lean_dec(v_a_645_);
v_a_831_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_761_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_761_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
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
v___jp_840_:
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_array_get_size(v_a_841_);
v___x_843_ = lean_nat_dec_eq(v___x_842_, v___x_839_);
if (v___x_843_ == 0)
{
lean_dec_ref(v_a_841_);
goto v___jp_694_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = lean_array_fget(v_a_841_, v___x_693_);
lean_dec_ref(v_a_841_);
v_a_644_ = v___x_844_;
goto _start;
}
}
v___jp_846_:
{
if (lean_obj_tag(v___y_847_) == 0)
{
lean_object* v_a_848_; 
v_a_848_ = lean_ctor_get(v___y_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___y_847_, 1);
v_a_841_ = v_a_848_;
goto v___jp_840_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_a_645_);
v_a_849_ = lean_ctor_get(v___y_847_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___y_847_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___y_847_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___y_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
v___jp_857_:
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_array_get_size(v_a_858_);
v___x_860_ = lean_nat_dec_eq(v___x_859_, v___x_839_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_a_858_);
goto v___jp_699_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_array_fget(v_a_858_, v___x_693_);
lean_dec_ref(v_a_858_);
v_a_644_ = v___x_861_;
goto _start;
}
}
v___jp_863_:
{
if (lean_obj_tag(v___y_864_) == 0)
{
lean_object* v_a_865_; 
v_a_865_ = lean_ctor_get(v___y_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___y_864_, 1);
v_a_858_ = v_a_865_;
goto v___jp_857_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_645_);
v_a_866_ = lean_ctor_get(v___y_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___y_864_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___y_864_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___y_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_695_ = lean_box(0);
v___x_696_ = lean_box(0);
v___x_697_ = l_Lean_Syntax_mkAntiquotNode(v___x_695_, v_a_645_, v___x_693_, v___x_696_, v___x_653_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
v___jp_699_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = lean_box(0);
v___x_701_ = lean_box(0);
v___x_702_ = l_Lean_Syntax_mkAntiquotNode(v___x_700_, v_a_645_, v___x_693_, v___x_701_, v___x_653_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
v___jp_704_:
{
lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_box(0);
v___x_707_ = 0;
v___x_708_ = l_Lean_Syntax_mkAntiquotNode(v___y_705_, v_a_645_, v___x_693_, v___x_706_, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
v___jp_710_:
{
lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_box(0);
v___x_713_ = 0;
v___x_714_ = l_Lean_Syntax_mkAntiquotNode(v___y_711_, v_a_645_, v___x_693_, v___x_712_, v___x_713_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
v___jp_716_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_717_ = lean_box(0);
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_Syntax_mkAntiquotNode(v___x_717_, v_a_645_, v___x_693_, v___x_718_, v___x_653_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
v___jp_654_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_655_ = lean_box(0);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_box(0);
v___x_658_ = l_Lean_Syntax_mkAntiquotNode(v___x_655_, v_a_645_, v___x_656_, v___x_657_, v___x_653_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_644_ = stack[0].m_obj;
lean_object* v_a_645_ = stack[1].m_obj;
lean_object* v_a_646_ = stack[2].m_obj;
lean_object* v_a_647_ = stack[3].m_obj;
lean_object* v_res_906_;
v_res_906_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_644_, v_a_645_, v_a_646_, v_a_647_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_912_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_913_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_913_ = stack[0].m_obj;
lean_object* v___y_914_ = stack[1].m_obj;
lean_object* v___y_915_ = stack[2].m_obj;
lean_object* v_res_918_;
v_res_918_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_913_, v___y_914_, v___y_915_);
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_923_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_924_, lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_925_, v___y_926_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_925_ = stack[1].m_obj;
lean_object* v___y_926_ = stack[2].m_obj;
lean_object* v___y_927_ = stack[3].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_box(0), v_msg_925_, v___y_926_, v___y_927_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_931_, lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_931_, v_msg_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_937_, lean_object* v_macroStack_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_937_, v_macroStack_938_, v___y_940_);
return v___x_942_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_937_ = stack[0].m_obj;
lean_object* v_macroStack_938_ = stack[1].m_obj;
lean_object* v___y_939_ = stack[2].m_obj;
lean_object* v___y_940_ = stack[3].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_937_, v_macroStack_938_, v___y_939_, v___y_940_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_944_, lean_object* v_macroStack_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_944_, v_macroStack_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_949_;
}
}
lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_953_, lean_object* v_stx_954_, lean_object* v_id_955_, lean_object* v_suffix_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_954_, v_id_955_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_975_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_975_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_965_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_953_, v_a_961_, v_suffix_956_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_mk_empty_array_with_capacity(v___x_966_);
v___x_968_ = lean_array_push(v___x_967_, v___x_965_);
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_970_ = lean_box(2);
v___x_971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
lean_ctor_set(v___x_971_, 2, v___x_968_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_971_);
v___x_973_ = v___x_963_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_dec_ref(v_suffix_956_);
lean_dec(v_kind_953_);
return v___x_960_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_953_ = stack[0].m_obj;
lean_object* v_stx_954_ = stack[1].m_obj;
lean_object* v_id_955_ = stack[2].m_obj;
lean_object* v_suffix_956_ = stack[3].m_obj;
lean_object* v_a_957_ = stack[4].m_obj;
lean_object* v_a_958_ = stack[5].m_obj;
lean_object* v_res_976_;
v_res_976_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_953_, v_stx_954_, v_id_955_, v_suffix_956_, v_a_957_, v_a_958_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_977_, lean_object* v_stx_978_, lean_object* v_id_979_, lean_object* v_suffix_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_977_, v_stx_978_, v_id_979_, v_suffix_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_984_;
}
}
lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_env_988_; lean_object* v___x_989_; lean_object* v_mainModule_990_; lean_object* v___x_991_; 
v___x_987_ = lean_st_ref_get(v___y_985_);
v_env_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_988_);
lean_dec(v___x_987_);
v___x_989_ = l_Lean_Environment_header(v_env_988_);
lean_dec_ref(v_env_988_);
v_mainModule_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_mainModule_990_);
lean_dec_ref(v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_mainModule_990_);
return v___x_991_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_985_ = stack[0].m_obj;
lean_object* v_res_992_;
v_res_992_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_985_);
stack->m_obj
 = v_res_992_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_993_);
lean_dec(v___y_993_);
return v_res_995_;
}
}
lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_997_);
return v___x_999_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_996_ = stack[0].m_obj;
lean_object* v___y_997_ = stack[1].m_obj;
lean_object* v_res_1000_;
v_res_1000_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_996_, v___y_997_);
stack->m_obj
 = v_res_1000_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1008_ = lean_panic_fn_borrowed(v___x_1007_, v_msg_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = l_Lean_maxRecDepthErrorMessage;
v___x_1015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_1017_ = l_Lean_MessageData_ofFormat(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_1019_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_1020_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1018_);
return v___x_1020_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_ref_1021_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1021_ = stack[0].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_1021_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_1030_, lean_object* v_declName_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___x_1034_; lean_object* v_env_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; 
v___x_1034_ = 0;
v_env_1035_ = l_Lean_Environment_setExporting(v_env_1030_, v___x_1034_);
lean_inc(v_declName_1031_);
v___x_1036_ = l_Lean_mkPrivateName(v_env_1035_, v_declName_1031_);
v___x_1037_ = 1;
lean_inc_ref(v_env_1035_);
v___x_1038_ = l_Lean_Environment_contains(v_env_1035_, v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1039_ = l_Lean_privateToUserName(v_declName_1031_);
v___x_1040_ = l_Lean_Environment_contains(v_env_1035_, v___x_1039_, v___x_1037_);
v___x_1041_ = lean_box(v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___y_1033_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declName_1031_);
v___x_1043_ = lean_box(v___x_1038_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___y_1033_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_1045_, lean_object* v_declName_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1045_, v_declName_1046_, v___y_1047_, v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1049_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_1050_, lean_object* v_i_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = lean_array_get_size(v_keys_1050_);
v___x_1054_ = lean_nat_dec_lt(v_i_1051_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v_i_1051_);
return v___x_1054_;
}
else
{
lean_object* v_k_x27_1055_; uint8_t v___x_1056_; 
v_k_x27_1055_ = lean_array_fget_borrowed(v_keys_1050_, v_i_1051_);
v___x_1056_ = l_Lean_instBEqExtraModUse_beq(v_k_1052_, v_k_x27_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_1051_, v___x_1057_);
lean_dec(v_i_1051_);
v_i_1051_ = v___x_1058_;
goto _start;
}
else
{
lean_dec(v_i_1051_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1050_ = stack[0].m_obj;
lean_object* v_i_1051_ = stack[1].m_obj;
lean_object* v_k_1052_ = stack[2].m_obj;
uint8_t v_res_1060_;
v_res_1060_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_1050_, v_i_1051_, v_k_1052_);
stack->m_num = v_res_1060_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_1061_, lean_object* v_i_1062_, lean_object* v_k_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_1061_, v_i_1062_, v_k_1063_);
lean_dec_ref(v_k_1063_);
lean_dec_ref(v_keys_1061_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_1066_, size_t v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 0)
{
lean_object* v_es_1069_; lean_object* v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; lean_object* v_j_1073_; lean_object* v___x_1074_; 
v_es_1069_ = lean_ctor_get(v_x_1066_, 0);
v___x_1070_ = lean_box(2);
v___x_1071_ = ((size_t)31ULL);
v___x_1072_ = lean_usize_land(v_x_1067_, v___x_1071_);
v_j_1073_ = lean_usize_to_nat(v___x_1072_);
v___x_1074_ = lean_array_get_borrowed(v___x_1070_, v_es_1069_, v_j_1073_);
lean_dec(v_j_1073_);
switch(lean_obj_tag(v___x_1074_))
{
case 0:
{
lean_object* v_key_1075_; uint8_t v___x_1076_; 
v_key_1075_ = lean_ctor_get(v___x_1074_, 0);
v___x_1076_ = l_Lean_instBEqExtraModUse_beq(v_x_1068_, v_key_1075_);
return v___x_1076_;
}
case 1:
{
lean_object* v_node_1077_; size_t v___x_1078_; size_t v___x_1079_; 
v_node_1077_ = lean_ctor_get(v___x_1074_, 0);
v___x_1078_ = ((size_t)5ULL);
v___x_1079_ = lean_usize_shift_right(v_x_1067_, v___x_1078_);
v_x_1066_ = v_node_1077_;
v_x_1067_ = v___x_1079_;
goto _start;
}
default: 
{
uint8_t v___x_1081_; 
v___x_1081_ = 0;
return v___x_1081_;
}
}
}
else
{
lean_object* v_ks_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v_ks_1082_ = lean_ctor_get(v_x_1066_, 0);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_1082_, v___x_1083_, v_x_1068_);
return v___x_1084_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1066_ = stack[0].m_obj;
size_t v_x_1067_ = stack[1].m_num;
lean_object* v_x_1068_ = stack[2].m_obj;
uint8_t v_res_1085_;
v_res_1085_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1066_, v_x_1067_, v_x_1068_);
stack->m_num = v_res_1085_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
size_t v_x_42706__boxed_1089_; uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_x_42706__boxed_1089_ = lean_unbox_usize(v_x_1087_);
lean_dec(v_x_1087_);
v_res_1090_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1086_, v_x_42706__boxed_1089_, v_x_1088_);
lean_dec_ref(v_x_1088_);
lean_dec_ref(v_x_1086_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
uint64_t v___x_1094_; size_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = l_Lean_instHashableExtraModUse_hash(v_x_1093_);
v___x_1095_ = lean_uint64_to_usize(v___x_1094_);
v___x_1096_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_1092_, v___x_1095_, v_x_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1092_ = stack[0].m_obj;
lean_object* v_x_1093_ = stack[1].m_obj;
uint8_t v_res_1097_;
v_res_1097_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_1092_, v_x_1093_);
stack->m_num = v_res_1097_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_1098_, v_x_1099_);
lean_dec_ref(v_x_1099_);
lean_dec_ref(v_x_1098_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1102_; double v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_float_of_nat(v___x_1102_);
return v___x_1103_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_1106_, lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Elab_Command_getRef___redArg(v___y_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1162_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_1107_, v___y_1109_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1162_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1162_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v_traceState_1119_; lean_object* v_env_1120_; lean_object* v_messages_1121_; lean_object* v_scopes_1122_; lean_object* v_usedQuotCtxts_1123_; lean_object* v_nextMacroScope_1124_; lean_object* v_maxRecDepth_1125_; lean_object* v_ngen_1126_; lean_object* v_auxDeclNGen_1127_; lean_object* v_infoState_1128_; lean_object* v_snapshotTasks_1129_; lean_object* v_prevLinterStates_1130_; lean_object* v_codeQualityEntryTasks_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1161_; 
v___x_1118_ = lean_st_ref_take(v___y_1109_);
v_traceState_1119_ = lean_ctor_get(v___x_1118_, 9);
v_env_1120_ = lean_ctor_get(v___x_1118_, 0);
v_messages_1121_ = lean_ctor_get(v___x_1118_, 1);
v_scopes_1122_ = lean_ctor_get(v___x_1118_, 2);
v_usedQuotCtxts_1123_ = lean_ctor_get(v___x_1118_, 3);
v_nextMacroScope_1124_ = lean_ctor_get(v___x_1118_, 4);
v_maxRecDepth_1125_ = lean_ctor_get(v___x_1118_, 5);
v_ngen_1126_ = lean_ctor_get(v___x_1118_, 6);
v_auxDeclNGen_1127_ = lean_ctor_get(v___x_1118_, 7);
v_infoState_1128_ = lean_ctor_get(v___x_1118_, 8);
v_snapshotTasks_1129_ = lean_ctor_get(v___x_1118_, 10);
v_prevLinterStates_1130_ = lean_ctor_get(v___x_1118_, 11);
v_codeQualityEntryTasks_1131_ = lean_ctor_get(v___x_1118_, 12);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1133_ = v___x_1118_;
v_isShared_1134_ = v_isSharedCheck_1161_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1131_);
lean_inc(v_prevLinterStates_1130_);
lean_inc(v_snapshotTasks_1129_);
lean_inc(v_traceState_1119_);
lean_inc(v_infoState_1128_);
lean_inc(v_auxDeclNGen_1127_);
lean_inc(v_ngen_1126_);
lean_inc(v_maxRecDepth_1125_);
lean_inc(v_nextMacroScope_1124_);
lean_inc(v_usedQuotCtxts_1123_);
lean_inc(v_scopes_1122_);
lean_inc(v_messages_1121_);
lean_inc(v_env_1120_);
lean_dec(v___x_1118_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1161_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint64_t v_tid_1135_; lean_object* v_traces_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1160_; 
v_tid_1135_ = lean_ctor_get_uint64(v_traceState_1119_, sizeof(void*)*1);
v_traces_1136_ = lean_ctor_get(v_traceState_1119_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_traceState_1119_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1138_ = v_traceState_1119_;
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_traces_1136_);
lean_dec(v_traceState_1119_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; double v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_1143_ = 0;
v___x_1144_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1145_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1145_, 0, v_cls_1106_);
lean_ctor_set(v___x_1145_, 1, v___x_1141_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
lean_ctor_set_float(v___x_1145_, sizeof(void*)*3, v___x_1142_);
lean_ctor_set_float(v___x_1145_, sizeof(void*)*3 + 8, v___x_1142_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3 + 16, v___x_1143_);
v___x_1146_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_1147_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v_a_1114_);
lean_ctor_set(v___x_1147_, 2, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1112_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_PersistentArray_push___redArg(v_traces_1136_, v___x_1148_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1149_);
v___x_1151_ = v___x_1138_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1149_);
lean_ctor_set_uint64(v_reuseFailAlloc_1159_, sizeof(void*)*1, v_tid_1135_);
v___x_1151_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 9, v___x_1151_);
v___x_1153_ = v___x_1133_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_env_1120_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_messages_1121_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_scopes_1122_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_usedQuotCtxts_1123_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_nextMacroScope_1124_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v_maxRecDepth_1125_);
lean_ctor_set(v_reuseFailAlloc_1158_, 6, v_ngen_1126_);
lean_ctor_set(v_reuseFailAlloc_1158_, 7, v_auxDeclNGen_1127_);
lean_ctor_set(v_reuseFailAlloc_1158_, 8, v_infoState_1128_);
lean_ctor_set(v_reuseFailAlloc_1158_, 9, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1158_, 10, v_snapshotTasks_1129_);
lean_ctor_set(v_reuseFailAlloc_1158_, 11, v_prevLinterStates_1130_);
lean_ctor_set(v_reuseFailAlloc_1158_, 12, v_codeQualityEntryTasks_1131_);
v___x_1153_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_st_ref_put(v___y_1109_, v___x_1153_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1140_);
v___x_1156_ = v___x_1116_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1140_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_msg_1107_);
lean_dec(v_cls_1106_);
v_a_1163_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1111_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1111_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1106_ = stack[0].m_obj;
lean_object* v_msg_1107_ = stack[1].m_obj;
lean_object* v___y_1108_ = stack[2].m_obj;
lean_object* v___y_1109_ = stack[3].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1106_, v_msg_1107_, v___y_1108_, v___y_1109_);
stack->m_obj
 = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1172_, lean_object* v_msg_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1172_, v_msg_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0(lean_object* v___x_1178_, lean_object* v_entry_1179_, lean_object* v_s_1180_){
_start:
{
lean_object* v_addEntryFn_1181_; lean_object* v_importedEntries_1182_; lean_object* v_state_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_addEntryFn_1181_ = lean_ctor_get(v___x_1178_, 3);
lean_inc(v_addEntryFn_1181_);
lean_dec_ref(v___x_1178_);
v_importedEntries_1182_ = lean_ctor_get(v_s_1180_, 0);
v_state_1183_ = lean_ctor_get(v_s_1180_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_s_1180_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v_s_1180_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_state_1183_);
lean_inc(v_importedEntries_1182_);
lean_dec(v_s_1180_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_state_1187_; lean_object* v___x_1189_; 
v_state_1187_ = lean_apply_2(v_addEntryFn_1181_, v_state_1183_, v_entry_1179_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_state_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_importedEntries_1182_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_state_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1192_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9(void){
_start:
{
lean_object* v_cls_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_cls_1205_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1206_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
v___x_1207_ = l_Lean_Name_append(v___x_1206_, v_cls_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1213_ = l_Lean_stringToMessageData(v___x_1212_);
return v___x_1213_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1218_, uint8_t v_isMeta_1219_, lean_object* v_hint_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_env_1245_; uint8_t v_isExporting_1246_; lean_object* v_entry_1247_; lean_object* v___x_1248_; lean_object* v_env_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0);
v___x_1244_ = lean_st_ref_get(v___y_1222_);
v_env_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_env_1245_);
lean_dec(v___x_1244_);
v_isExporting_1246_ = lean_ctor_get_uint8(v_env_1245_, sizeof(void*)*13);
lean_dec_ref(v_env_1245_);
lean_inc(v_mod_1218_);
v_entry_1247_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1247_, 0, v_mod_1218_);
lean_ctor_set_uint8(v_entry_1247_, sizeof(void*)*1, v_isExporting_1246_);
lean_ctor_set_uint8(v_entry_1247_, sizeof(void*)*1 + 1, v_isMeta_1219_);
v___x_1248_ = lean_st_ref_get(v___y_1222_);
v_env_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_env_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1251_ = lean_box(1);
v___x_1252_ = lean_box(0);
v___x_1253_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1243_, v___x_1250_, v_env_1249_, v___x_1251_, v___x_1252_);
v___x_1254_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1253_, v_entry_1247_);
lean_dec(v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___f_1255_; uint8_t v___x_1256_; lean_object* v___y_1258_; lean_object* v_cls_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v_scopes_1305_; lean_object* v___x_1306_; lean_object* v_opts_1307_; uint8_t v_hasTrace_1308_; 
v___f_1255_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_1255_, 0, v___x_1250_);
lean_closure_set(v___f_1255_, 1, v_entry_1247_);
v___x_1256_ = 1;
v_cls_1280_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1281_ = l_Lean_inheritedTraceOptions;
v___x_1282_ = lean_st_ref_get(v___x_1281_);
v___x_1283_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1284_ = lean_st_ref_get(v___y_1222_);
v_scopes_1305_ = lean_ctor_get(v___x_1284_, 2);
lean_inc(v_scopes_1305_);
lean_dec(v___x_1284_);
v___x_1306_ = l_List_head_x21___redArg(v___x_1283_, v_scopes_1305_);
lean_dec(v_scopes_1305_);
v_opts_1307_ = lean_ctor_get(v___x_1306_, 1);
lean_inc_ref(v_opts_1307_);
lean_dec(v___x_1306_);
v_hasTrace_1308_ = lean_ctor_get_uint8(v_opts_1307_, sizeof(void*)*1);
if (v_hasTrace_1308_ == 0)
{
lean_dec_ref(v_opts_1307_);
lean_dec(v___x_1282_);
lean_dec(v_hint_1220_);
lean_dec(v_mod_1218_);
v___y_1258_ = v___y_1222_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9);
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1282_, v_opts_1307_, v___x_1309_);
lean_dec_ref(v_opts_1307_);
lean_dec(v___x_1282_);
if (v___x_1310_ == 0)
{
lean_dec(v_hint_1220_);
lean_dec(v_mod_1218_);
v___y_1258_ = v___y_1222_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1311_; lean_object* v___y_1313_; 
v___x_1311_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
if (v_isExporting_1246_ == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1313_ = v___x_1320_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1313_ = v___x_1321_;
goto v___jp_1312_;
}
v___jp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_inc_ref(v___y_1313_);
v___x_1314_ = l_Lean_stringToMessageData(v___y_1313_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1311_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
if (v_isMeta_1219_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___y_1291_ = v___x_1317_;
v___y_1292_ = v___x_1318_;
goto v___jp_1290_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15));
v___y_1291_ = v___x_1317_;
v___y_1292_ = v___x_1319_;
goto v___jp_1290_;
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v_toEnvExtension_1260_; lean_object* v_env_1261_; lean_object* v_messages_1262_; lean_object* v_scopes_1263_; lean_object* v_usedQuotCtxts_1264_; lean_object* v_nextMacroScope_1265_; lean_object* v_maxRecDepth_1266_; lean_object* v_ngen_1267_; lean_object* v_auxDeclNGen_1268_; lean_object* v_infoState_1269_; lean_object* v_traceState_1270_; lean_object* v_snapshotTasks_1271_; lean_object* v_prevLinterStates_1272_; lean_object* v_codeQualityEntryTasks_1273_; lean_object* v_asyncMode_1274_; uint8_t v_logWrites_1275_; lean_object* v___x_1276_; 
v___x_1259_ = lean_st_ref_take(v___y_1258_);
v_toEnvExtension_1260_ = lean_ctor_get(v___x_1250_, 0);
v_env_1261_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1261_);
v_messages_1262_ = lean_ctor_get(v___x_1259_, 1);
lean_inc_ref(v_messages_1262_);
v_scopes_1263_ = lean_ctor_get(v___x_1259_, 2);
lean_inc(v_scopes_1263_);
v_usedQuotCtxts_1264_ = lean_ctor_get(v___x_1259_, 3);
lean_inc(v_usedQuotCtxts_1264_);
v_nextMacroScope_1265_ = lean_ctor_get(v___x_1259_, 4);
lean_inc(v_nextMacroScope_1265_);
v_maxRecDepth_1266_ = lean_ctor_get(v___x_1259_, 5);
lean_inc(v_maxRecDepth_1266_);
v_ngen_1267_ = lean_ctor_get(v___x_1259_, 6);
lean_inc_ref(v_ngen_1267_);
v_auxDeclNGen_1268_ = lean_ctor_get(v___x_1259_, 7);
lean_inc_ref(v_auxDeclNGen_1268_);
v_infoState_1269_ = lean_ctor_get(v___x_1259_, 8);
lean_inc_ref(v_infoState_1269_);
v_traceState_1270_ = lean_ctor_get(v___x_1259_, 9);
lean_inc_ref(v_traceState_1270_);
v_snapshotTasks_1271_ = lean_ctor_get(v___x_1259_, 10);
lean_inc_ref(v_snapshotTasks_1271_);
v_prevLinterStates_1272_ = lean_ctor_get(v___x_1259_, 11);
lean_inc(v_prevLinterStates_1272_);
v_codeQualityEntryTasks_1273_ = lean_ctor_get(v___x_1259_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1273_);
lean_dec(v___x_1259_);
v_asyncMode_1274_ = lean_ctor_get(v_toEnvExtension_1260_, 2);
v_logWrites_1275_ = lean_ctor_get_uint8(v_toEnvExtension_1260_, sizeof(void*)*6);
v___x_1276_ = lean_box(0);
if (v_logWrites_1275_ == 0)
{
lean_object* v___x_1277_; 
lean_inc_ref(v_toEnvExtension_1260_);
v___x_1277_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1260_, v_env_1261_, v___f_1255_, v_asyncMode_1274_, v___x_1252_, v___x_1256_);
v___y_1225_ = v_scopes_1263_;
v___y_1226_ = v_nextMacroScope_1265_;
v___y_1227_ = v_maxRecDepth_1266_;
v___y_1228_ = v_codeQualityEntryTasks_1273_;
v___y_1229_ = v_auxDeclNGen_1268_;
v___y_1230_ = v___y_1258_;
v___y_1231_ = v_usedQuotCtxts_1264_;
v___y_1232_ = v_ngen_1267_;
v___y_1233_ = v_messages_1262_;
v___y_1234_ = v___x_1276_;
v___y_1235_ = v_infoState_1269_;
v___y_1236_ = v_traceState_1270_;
v___y_1237_ = v_prevLinterStates_1272_;
v___y_1238_ = v_snapshotTasks_1271_;
v___y_1239_ = v___x_1277_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_inc_ref_n(v_toEnvExtension_1260_, 2);
v___x_1278_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1260_, v_env_1261_);
lean_dec_ref(v_env_1261_);
v___x_1279_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1260_, v___x_1278_, v___f_1255_, v_asyncMode_1274_, v___x_1252_, v___x_1256_);
v___y_1225_ = v_scopes_1263_;
v___y_1226_ = v_nextMacroScope_1265_;
v___y_1227_ = v_maxRecDepth_1266_;
v___y_1228_ = v_codeQualityEntryTasks_1273_;
v___y_1229_ = v_auxDeclNGen_1268_;
v___y_1230_ = v___y_1258_;
v___y_1231_ = v_usedQuotCtxts_1264_;
v___y_1232_ = v_ngen_1267_;
v___y_1233_ = v_messages_1262_;
v___y_1234_ = v___x_1276_;
v___y_1235_ = v_infoState_1269_;
v___y_1236_ = v_traceState_1270_;
v___y_1237_ = v_prevLinterStates_1272_;
v___y_1238_ = v_snapshotTasks_1271_;
v___y_1239_ = v___x_1279_;
goto v___jp_1224_;
}
}
v___jp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___y_1286_);
lean_ctor_set(v___x_1288_, 1, v___y_1287_);
v___x_1289_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1280_, v___x_1288_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
v___y_1258_ = v___y_1222_;
goto v___jp_1257_;
}
else
{
lean_dec_ref(v___f_1255_);
return v___x_1289_;
}
}
v___jp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
lean_inc_ref(v___y_1292_);
v___x_1293_ = l_Lean_stringToMessageData(v___y_1292_);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___y_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_MessageData_ofName(v_mod_1218_);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_Name_isAnonymous(v_hint_1220_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1301_ = l_Lean_MessageData_ofName(v_hint_1220_);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___y_1286_ = v___x_1298_;
v___y_1287_ = v___x_1302_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_hint_1220_);
v___x_1303_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
v___y_1286_ = v___x_1298_;
v___y_1287_ = v___x_1304_;
goto v___jp_1285_;
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec_ref_known(v_entry_1247_, 1);
lean_dec(v_hint_1220_);
lean_dec(v_mod_1218_);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
v___jp_1224_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1239_);
lean_ctor_set(v___x_1240_, 1, v___y_1233_);
lean_ctor_set(v___x_1240_, 2, v___y_1225_);
lean_ctor_set(v___x_1240_, 3, v___y_1231_);
lean_ctor_set(v___x_1240_, 4, v___y_1226_);
lean_ctor_set(v___x_1240_, 5, v___y_1227_);
lean_ctor_set(v___x_1240_, 6, v___y_1232_);
lean_ctor_set(v___x_1240_, 7, v___y_1229_);
lean_ctor_set(v___x_1240_, 8, v___y_1235_);
lean_ctor_set(v___x_1240_, 9, v___y_1236_);
lean_ctor_set(v___x_1240_, 10, v___y_1238_);
lean_ctor_set(v___x_1240_, 11, v___y_1237_);
lean_ctor_set(v___x_1240_, 12, v___y_1228_);
v___x_1241_ = lean_st_ref_put(v___y_1230_, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1234_);
return v___x_1242_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1218_ = stack[0].m_obj;
uint8_t v_isMeta_1219_ = stack[1].m_num;
lean_object* v_hint_1220_ = stack[2].m_obj;
lean_object* v___y_1221_ = stack[3].m_obj;
lean_object* v___y_1222_ = stack[4].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1218_, v_isMeta_1219_, v_hint_1220_, v___y_1221_, v___y_1222_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1325_, lean_object* v_isMeta_1326_, lean_object* v_hint_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_isMeta_boxed_1331_; lean_object* v_res_1332_; 
v_isMeta_boxed_1331_ = lean_unbox(v_isMeta_1326_);
v_res_1332_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1325_, v_isMeta_boxed_1331_, v_hint_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1332_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1333_, lean_object* v_declName_1334_, lean_object* v_as_1335_, size_t v_sz_1336_, size_t v_i_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_lt(v_i_1337_, v_sz_1336_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec(v_declName_1334_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_b_1338_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v_modules_1345_; lean_object* v___x_1346_; lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v_toImport_1349_; lean_object* v_module_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1344_ = l_Lean_Environment_header(v___x_1333_);
v_modules_1345_ = lean_ctor_get(v___x_1344_, 3);
lean_inc_ref(v_modules_1345_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1347_ = lean_array_uget_borrowed(v_as_1335_, v_i_1337_);
v___x_1348_ = lean_array_get(v___x_1346_, v_modules_1345_, v_a_1347_);
lean_dec_ref(v_modules_1345_);
v_toImport_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_ref(v_toImport_1349_);
lean_dec(v___x_1348_);
v_module_1350_ = lean_ctor_get(v_toImport_1349_, 0);
lean_inc(v_module_1350_);
lean_dec_ref(v_toImport_1349_);
v___x_1351_ = lean_box(0);
v___x_1352_ = 0;
lean_inc(v_declName_1334_);
v___x_1353_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1350_, v___x_1352_, v_declName_1334_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1353_) == 0)
{
size_t v___x_1354_; size_t v___x_1355_; 
lean_dec_ref_known(v___x_1353_, 1);
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = lean_usize_add(v_i_1337_, v___x_1354_);
v_i_1337_ = v___x_1355_;
v_b_1338_ = v___x_1351_;
goto _start;
}
else
{
lean_dec(v_declName_1334_);
return v___x_1353_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1333_ = stack[0].m_obj;
lean_object* v_declName_1334_ = stack[1].m_obj;
lean_object* v_as_1335_ = stack[2].m_obj;
size_t v_sz_1336_ = stack[3].m_num;
size_t v_i_1337_ = stack[4].m_num;
lean_object* v_b_1338_ = stack[5].m_obj;
lean_object* v___y_1339_ = stack[6].m_obj;
lean_object* v___y_1340_ = stack[7].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1333_, v_declName_1334_, v_as_1335_, v_sz_1336_, v_i_1337_, v_b_1338_, v___y_1339_, v___y_1340_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1358_, lean_object* v_declName_1359_, lean_object* v_as_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1358_, v_declName_1359_, v_as_1360_, v_sz_boxed_1367_, v_i_boxed_1368_, v_b_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec_ref(v_as_1360_);
lean_dec_ref(v___x_1358_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1370_, lean_object* v_x_1371_){
_start:
{
if (lean_obj_tag(v_x_1371_) == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
else
{
lean_object* v_key_1373_; lean_object* v_value_1374_; lean_object* v_tail_1375_; uint8_t v___x_1376_; 
v_key_1373_ = lean_ctor_get(v_x_1371_, 0);
v_value_1374_ = lean_ctor_get(v_x_1371_, 1);
v_tail_1375_ = lean_ctor_get(v_x_1371_, 2);
v___x_1376_ = lean_name_eq(v_key_1373_, v_a_1370_);
if (v___x_1376_ == 0)
{
v_x_1371_ = v_tail_1375_;
goto _start;
}
else
{
lean_object* v___x_1378_; 
lean_inc(v_value_1374_);
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_value_1374_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1379_, v_x_1380_);
lean_dec(v_x_1380_);
lean_dec(v_a_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_buckets_1384_; lean_object* v___x_1385_; uint64_t v___y_1387_; 
v_buckets_1384_ = lean_ctor_get(v_m_1382_, 1);
v___x_1385_ = lean_array_get_size(v_buckets_1384_);
if (lean_obj_tag(v_a_1383_) == 0)
{
uint64_t v___x_1401_; 
v___x_1401_ = 1723ULL;
v___y_1387_ = v___x_1401_;
goto v___jp_1386_;
}
else
{
uint64_t v_hash_1402_; 
v_hash_1402_ = lean_ctor_get_uint64(v_a_1383_, sizeof(void*)*2);
v___y_1387_ = v_hash_1402_;
goto v___jp_1386_;
}
v___jp_1386_:
{
uint64_t v___x_1388_; uint64_t v___x_1389_; uint64_t v_fold_1390_; uint64_t v___x_1391_; uint64_t v___x_1392_; uint64_t v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1388_ = 32ULL;
v___x_1389_ = lean_uint64_shift_right(v___y_1387_, v___x_1388_);
v_fold_1390_ = lean_uint64_xor(v___y_1387_, v___x_1389_);
v___x_1391_ = 16ULL;
v___x_1392_ = lean_uint64_shift_right(v_fold_1390_, v___x_1391_);
v___x_1393_ = lean_uint64_xor(v_fold_1390_, v___x_1392_);
v___x_1394_ = lean_uint64_to_usize(v___x_1393_);
v___x_1395_ = lean_usize_of_nat(v___x_1385_);
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_sub(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_usize_land(v___x_1394_, v___x_1397_);
v___x_1399_ = lean_array_uget_borrowed(v_buckets_1384_, v___x_1398_);
v___x_1400_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1383_, v___x_1399_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_m_1403_);
return v_res_1405_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1406_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1409_, uint8_t v_isMeta_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_env_1419_; lean_object* v___y_1421_; lean_object* v___x_1434_; 
v___x_1414_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0);
v___x_1415_ = lean_st_ref_get(v___y_1412_);
v_env_1419_ = lean_ctor_get(v___x_1415_, 0);
lean_inc_ref(v_env_1419_);
lean_dec(v___x_1415_);
v___x_1434_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1419_, v_declName_1409_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref(v_env_1419_);
lean_dec(v_declName_1409_);
goto v___jp_1416_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1436_; lean_object* v_modules_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_val_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = l_Lean_Environment_header(v_env_1419_);
v_modules_1437_ = lean_ctor_get(v___x_1436_, 3);
lean_inc_ref(v_modules_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = lean_array_get_size(v_modules_1437_);
v___x_1439_ = lean_nat_dec_lt(v_val_1435_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_dec_ref(v_modules_1437_);
lean_dec(v_val_1435_);
lean_dec_ref(v_env_1419_);
lean_dec(v_declName_1409_);
goto v___jp_1416_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___y_1443_; 
v___x_1440_ = lean_array_fget(v_modules_1437_, v_val_1435_);
lean_dec(v_val_1435_);
lean_dec_ref(v_modules_1437_);
v___x_1441_ = lean_st_ref_get(v___y_1412_);
if (v_isMeta_1410_ == 0)
{
lean_dec(v___x_1441_);
v___y_1443_ = v_isMeta_1410_;
goto v___jp_1442_;
}
else
{
lean_object* v_env_1454_; uint8_t v___x_1455_; 
v_env_1454_ = lean_ctor_get(v___x_1441_, 0);
lean_inc_ref(v_env_1454_);
lean_dec(v___x_1441_);
lean_inc(v_declName_1409_);
v___x_1455_ = l_Lean_isMarkedMeta(v_env_1454_, v_declName_1409_);
if (v___x_1455_ == 0)
{
v___y_1443_ = v_isMeta_1410_;
goto v___jp_1442_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = 0;
v___y_1443_ = v___x_1456_;
goto v___jp_1442_;
}
}
v___jp_1442_:
{
lean_object* v_toImport_1444_; lean_object* v_module_1445_; lean_object* v___x_1446_; 
v_toImport_1444_ = lean_ctor_get(v___x_1440_, 0);
lean_inc_ref(v_toImport_1444_);
lean_dec(v___x_1440_);
v_module_1445_ = lean_ctor_get(v_toImport_1444_, 0);
lean_inc(v_module_1445_);
lean_dec_ref(v_toImport_1444_);
lean_inc(v_declName_1409_);
v___x_1446_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1445_, v___y_1443_, v_declName_1409_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref_known(v___x_1446_, 1);
v___x_1447_ = l_Lean_indirectModUseExt;
v___x_1448_ = lean_box(1);
v___x_1449_ = lean_box(0);
lean_inc_ref(v_env_1419_);
v___x_1450_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1414_, v___x_1447_, v_env_1419_, v___x_1448_, v___x_1449_);
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1450_, v_declName_1409_);
lean_dec(v___x_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___y_1421_ = v___x_1452_;
goto v___jp_1420_;
}
else
{
lean_object* v_val_1453_; 
v_val_1453_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v___x_1451_, 1);
v___y_1421_ = v_val_1453_;
goto v___jp_1420_;
}
}
else
{
lean_dec_ref(v_env_1419_);
lean_dec(v_declName_1409_);
return v___x_1446_;
}
}
}
}
v___jp_1416_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
v___jp_1420_:
{
lean_object* v___x_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1422_ = lean_box(0);
v_sz_1423_ = lean_array_size(v___y_1421_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1419_, v_declName_1409_, v___y_1421_, v_sz_1423_, v___x_1424_, v___x_1422_, v___y_1411_, v___y_1412_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v_env_1419_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___x_1425_, 0);
lean_dec(v_unused_1433_);
v___x_1427_ = v___x_1425_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v___x_1425_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1422_);
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1422_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
else
{
return v___x_1425_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1409_ = stack[0].m_obj;
uint8_t v_isMeta_1410_ = stack[1].m_num;
lean_object* v___y_1411_ = stack[2].m_obj;
lean_object* v___y_1412_ = stack[3].m_obj;
lean_object* v_res_1457_;
v_res_1457_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1409_, v_isMeta_1410_, v___y_1411_, v___y_1412_);
stack->m_obj
 = v_res_1457_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1458_, lean_object* v_isMeta_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_isMeta_boxed_1463_; lean_object* v_res_1464_; 
v_isMeta_boxed_1463_ = lean_unbox(v_isMeta_1459_);
v_res_1464_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1458_, v_isMeta_boxed_1463_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v_res_1464_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
if (lean_obj_tag(v_as_x27_1465_) == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1466_);
return v___x_1470_;
}
else
{
lean_object* v_head_1471_; lean_object* v_tail_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; 
v_head_1471_ = lean_ctor_get(v_as_x27_1465_, 0);
v_tail_1472_ = lean_ctor_get(v_as_x27_1465_, 1);
v___x_1473_ = lean_box(0);
v___x_1474_ = 1;
lean_inc(v_head_1471_);
v___x_1475_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1471_, v___x_1474_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_dec_ref_known(v___x_1475_, 1);
v_as_x27_1465_ = v_tail_1472_;
v_b_1466_ = v___x_1473_;
goto _start;
}
else
{
return v___x_1475_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1465_ = stack[0].m_obj;
lean_object* v_b_1466_ = stack[1].m_obj;
lean_object* v___y_1467_ = stack[2].m_obj;
lean_object* v___y_1468_ = stack[3].m_obj;
lean_object* v_res_1477_;
v_res_1477_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1465_, v_b_1466_, v___y_1467_, v___y_1468_);
stack->m_obj
 = v_res_1477_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1478_, v_b_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v_as_x27_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1484_, lean_object* v_opts_1485_, lean_object* v_currNamespace_1486_, lean_object* v_openDecls_1487_, lean_object* v_n_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = l_Lean_ResolveName_resolveGlobalName(v_env_1484_, v_opts_1485_, v_currNamespace_1486_, v_openDecls_1487_, v_n_1488_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___y_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1493_, lean_object* v_opts_1494_, lean_object* v_currNamespace_1495_, lean_object* v_openDecls_1496_, lean_object* v_n_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1493_, v_opts_1494_, v_currNamespace_1495_, v_openDecls_1496_, v_n_1497_, v___y_1498_, v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_opts_1494_);
return v_res_1500_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1501_, lean_object* v_msg_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Elab_Command_getRef___redArg(v___y_1503_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v_fileName_1508_; lean_object* v_fileMap_1509_; lean_object* v_currRecDepth_1510_; lean_object* v_cmdPos_1511_; lean_object* v_macroStack_1512_; lean_object* v_quotContext_x3f_1513_; lean_object* v_currMacroScope_1514_; lean_object* v_snap_x3f_1515_; lean_object* v_cancelTk_x3f_1516_; uint8_t v_suppressElabErrors_1517_; lean_object* v_ref_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v_fileName_1508_ = lean_ctor_get(v___y_1503_, 0);
v_fileMap_1509_ = lean_ctor_get(v___y_1503_, 1);
v_currRecDepth_1510_ = lean_ctor_get(v___y_1503_, 2);
v_cmdPos_1511_ = lean_ctor_get(v___y_1503_, 3);
v_macroStack_1512_ = lean_ctor_get(v___y_1503_, 4);
v_quotContext_x3f_1513_ = lean_ctor_get(v___y_1503_, 5);
v_currMacroScope_1514_ = lean_ctor_get(v___y_1503_, 6);
v_snap_x3f_1515_ = lean_ctor_get(v___y_1503_, 8);
v_cancelTk_x3f_1516_ = lean_ctor_get(v___y_1503_, 9);
v_suppressElabErrors_1517_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*10);
v_ref_1518_ = l_Lean_replaceRef(v_ref_1501_, v_a_1507_);
lean_dec(v_a_1507_);
lean_inc(v_cancelTk_x3f_1516_);
lean_inc(v_snap_x3f_1515_);
lean_inc(v_currMacroScope_1514_);
lean_inc(v_quotContext_x3f_1513_);
lean_inc(v_macroStack_1512_);
lean_inc(v_cmdPos_1511_);
lean_inc(v_currRecDepth_1510_);
lean_inc_ref(v_fileMap_1509_);
lean_inc_ref(v_fileName_1508_);
v___x_1519_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1519_, 0, v_fileName_1508_);
lean_ctor_set(v___x_1519_, 1, v_fileMap_1509_);
lean_ctor_set(v___x_1519_, 2, v_currRecDepth_1510_);
lean_ctor_set(v___x_1519_, 3, v_cmdPos_1511_);
lean_ctor_set(v___x_1519_, 4, v_macroStack_1512_);
lean_ctor_set(v___x_1519_, 5, v_quotContext_x3f_1513_);
lean_ctor_set(v___x_1519_, 6, v_currMacroScope_1514_);
lean_ctor_set(v___x_1519_, 7, v_ref_1518_);
lean_ctor_set(v___x_1519_, 8, v_snap_x3f_1515_);
lean_ctor_set(v___x_1519_, 9, v_cancelTk_x3f_1516_);
lean_ctor_set_uint8(v___x_1519_, sizeof(void*)*10, v_suppressElabErrors_1517_);
v___x_1520_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1502_, v___x_1519_, v___y_1504_);
lean_dec_ref_known(v___x_1519_, 10);
return v___x_1520_;
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_msg_1502_);
v_a_1521_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1506_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1506_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1501_ = stack[0].m_obj;
lean_object* v_msg_1502_ = stack[1].m_obj;
lean_object* v___y_1503_ = stack[2].m_obj;
lean_object* v___y_1504_ = stack[3].m_obj;
lean_object* v_res_1529_;
v_res_1529_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1501_, v_msg_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1529_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1530_, lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1530_, v_msg_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v_ref_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1536_, lean_object* v_currNamespace_1537_, lean_object* v_openDecls_1538_, lean_object* v_n_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_ResolveName_resolveNamespace(v_env_1536_, v_currNamespace_1537_, v_openDecls_1538_, v_n_1539_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1544_, lean_object* v_currNamespace_1545_, lean_object* v_openDecls_1546_, lean_object* v_n_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1544_, v_currNamespace_1545_, v_openDecls_1546_, v_n_1547_, v___y_1548_, v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_currNamespace_1551_);
lean_ctor_set(v___x_1554_, 1, v___y_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1555_, v___y_1556_, v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1559_, lean_object* v___y_1560_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_a_1561_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_a_1561_);
lean_ctor_set(v___x_1562_, 1, v___y_1560_);
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_a_1563_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1563_);
lean_ctor_set(v___x_1564_, 1, v___y_1560_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1565_, v___y_1566_);
lean_dec_ref(v_x_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1568_, lean_object* v_stx_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1568_, v_stx_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
if (lean_obj_tag(v_a_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v_a_1574_ = lean_ctor_get(v___x_1572_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1572_, 0);
lean_dec(v_unused_1583_);
v___x_1576_ = v___x_1572_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = lean_box(0);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_a_1574_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1612_; 
v_val_1584_ = lean_ctor_get(v_a_1573_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1573_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1586_ = v_a_1573_;
v_isShared_1587_ = v_isSharedCheck_1612_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_val_1584_);
lean_dec(v_a_1573_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1612_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_snd_1588_; 
v_snd_1588_ = lean_ctor_get(v_val_1584_, 1);
lean_inc(v_snd_1588_);
lean_dec(v_val_1584_);
if (lean_obj_tag(v_snd_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
lean_del_object(v___x_1586_);
v_a_1589_ = lean_ctor_get(v___x_1572_, 1);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1572_, 2);
v_a_1590_ = lean_ctor_get(v_snd_1588_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_snd_1588_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1592_ = v_snd_1588_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v_snd_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1595_, v_a_1589_);
lean_dec_ref(v___x_1595_);
return v___x_1596_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1611_; 
v_a_1599_ = lean_ctor_get(v___x_1572_, 1);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1572_, 2);
v_a_1600_ = lean_ctor_get(v_snd_1588_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_snd_1588_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1602_ = v_snd_1588_;
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v_snd_1588_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_a_1600_);
v___x_1605_ = v___x_1586_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1605_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1607_, v_a_1599_);
lean_dec_ref(v___x_1607_);
return v___x_1608_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1613_ = lean_ctor_get(v___x_1572_, 0);
v_a_1614_ = lean_ctor_get(v___x_1572_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1572_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_inc(v_a_1613_);
lean_dec(v___x_1572_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1613_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1622_, lean_object* v_stx_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1622_, v_stx_1623_, v___y_1624_, v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1626_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v___x_1627_);
return v___x_1629_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1633_;
v_res_1633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1635_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
if (lean_obj_tag(v_as_1636_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
else
{
lean_object* v_head_1642_; lean_object* v_tail_1643_; lean_object* v_fst_1644_; lean_object* v_snd_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_scopes_1650_; lean_object* v___x_1651_; lean_object* v_opts_1652_; uint8_t v_hasTrace_1653_; 
v_head_1642_ = lean_ctor_get(v_as_1636_, 0);
lean_inc(v_head_1642_);
v_tail_1643_ = lean_ctor_get(v_as_1636_, 1);
lean_inc(v_tail_1643_);
lean_dec_ref_known(v_as_1636_, 2);
v_fst_1644_ = lean_ctor_get(v_head_1642_, 0);
lean_inc(v_fst_1644_);
v_snd_1645_ = lean_ctor_get(v_head_1642_, 1);
lean_inc(v_snd_1645_);
lean_dec(v_head_1642_);
v___x_1646_ = l_Lean_inheritedTraceOptions;
v___x_1647_ = lean_st_ref_get(v___x_1646_);
v___x_1648_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1649_ = lean_st_ref_get(v___y_1638_);
v_scopes_1650_ = lean_ctor_get(v___x_1649_, 2);
lean_inc(v_scopes_1650_);
lean_dec(v___x_1649_);
v___x_1651_ = l_List_head_x21___redArg(v___x_1648_, v_scopes_1650_);
lean_dec(v_scopes_1650_);
v_opts_1652_ = lean_ctor_get(v___x_1651_, 1);
lean_inc_ref(v_opts_1652_);
lean_dec(v___x_1651_);
v_hasTrace_1653_ = lean_ctor_get_uint8(v_opts_1652_, sizeof(void*)*1);
if (v_hasTrace_1653_ == 0)
{
lean_dec_ref(v_opts_1652_);
lean_dec(v___x_1647_);
lean_dec(v_snd_1645_);
lean_dec(v_fst_1644_);
v_as_1636_ = v_tail_1643_;
goto _start;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
lean_inc(v_fst_1644_);
v___x_1656_ = l_Lean_Name_append(v___x_1655_, v_fst_1644_);
v___x_1657_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1647_, v_opts_1652_, v___x_1656_);
lean_dec(v___x_1656_);
lean_dec_ref(v_opts_1652_);
lean_dec(v___x_1647_);
if (v___x_1657_ == 0)
{
lean_dec(v_snd_1645_);
lean_dec(v_fst_1644_);
v_as_1636_ = v_tail_1643_;
goto _start;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_snd_1645_);
v___x_1660_ = l_Lean_MessageData_ofFormat(v___x_1659_);
v___x_1661_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1644_, v___x_1660_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec_ref_known(v___x_1661_, 1);
v_as_1636_ = v_tail_1643_;
goto _start;
}
else
{
lean_dec(v_tail_1643_);
return v___x_1661_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1636_ = stack[0].m_obj;
lean_object* v___y_1637_ = stack[1].m_obj;
lean_object* v___y_1638_ = stack[2].m_obj;
lean_object* v_res_1663_;
v_res_1663_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1636_, v___y_1637_, v___y_1638_);
stack->m_obj
 = v_res_1663_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1668_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v_env_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_scopes_1680_; lean_object* v___x_1681_; lean_object* v_opts_1682_; lean_object* v___x_1683_; 
v___x_1674_ = lean_st_ref_get(v___y_1672_);
v_env_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc_ref_n(v_env_1675_, 3);
lean_dec(v___x_1674_);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1676_, 0, v_env_1675_);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1677_, 0, v_env_1675_);
v___x_1678_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1679_ = lean_st_ref_get(v___y_1672_);
v_scopes_1680_ = lean_ctor_get(v___x_1679_, 2);
lean_inc(v_scopes_1680_);
lean_dec(v___x_1679_);
v___x_1681_ = l_List_head_x21___redArg(v___x_1678_, v_scopes_1680_);
lean_dec(v_scopes_1680_);
v_opts_1682_ = lean_ctor_get(v___x_1681_, 1);
lean_inc_ref(v_opts_1682_);
lean_dec(v___x_1681_);
v___x_1683_ = l_Lean_Elab_Command_getScope___redArg(v___y_1672_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_currNamespace_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v_currNamespace_1685_ = lean_ctor_get(v_a_1684_, 2);
lean_inc_n(v_currNamespace_1685_, 2);
lean_dec(v_a_1684_);
v___f_1686_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1686_, 0, v_currNamespace_1685_);
v___x_1687_ = l_Lean_Elab_Command_getScope___redArg(v___y_1672_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v_openDecls_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v_methods_1692_; lean_object* v___x_1693_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v_openDecls_1689_ = lean_ctor_get(v_a_1688_, 3);
lean_inc_n(v_openDecls_1689_, 2);
lean_dec(v_a_1688_);
lean_inc(v_currNamespace_1685_);
lean_inc_ref(v_env_1675_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1690_, 0, v_env_1675_);
lean_closure_set(v___f_1690_, 1, v_currNamespace_1685_);
lean_closure_set(v___f_1690_, 2, v_openDecls_1689_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1691_, 0, v_env_1675_);
lean_closure_set(v___f_1691_, 1, v_opts_1682_);
lean_closure_set(v___f_1691_, 2, v_currNamespace_1685_);
lean_closure_set(v___f_1691_, 3, v_openDecls_1689_);
v_methods_1692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1692_, 0, v___f_1677_);
lean_ctor_set(v_methods_1692_, 1, v___f_1686_);
lean_ctor_set(v_methods_1692_, 2, v___f_1676_);
lean_ctor_set(v_methods_1692_, 3, v___f_1690_);
lean_ctor_set(v_methods_1692_, 4, v___f_1691_);
v___x_1693_ = l_Lean_Elab_Command_getRef___redArg(v___y_1671_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1671_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_currRecDepth_1697_; lean_object* v_quotContext_x3f_1698_; lean_object* v_a_1700_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v_currRecDepth_1697_ = lean_ctor_get(v___y_1671_, 2);
v_quotContext_x3f_1698_ = lean_ctor_get(v___y_1671_, 5);
if (lean_obj_tag(v_quotContext_x3f_1698_) == 0)
{
lean_object* v___x_1774_; lean_object* v_a_1775_; 
v___x_1774_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1672_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v_a_1700_ = v_a_1775_;
goto v___jp_1699_;
}
else
{
lean_object* v_val_1776_; 
v_val_1776_ = lean_ctor_get(v_quotContext_x3f_1698_, 0);
lean_inc(v_val_1776_);
v_a_1700_ = v_val_1776_;
goto v___jp_1699_;
}
v___jp_1699_:
{
lean_object* v___x_1701_; lean_object* v_maxRecDepth_1702_; lean_object* v___x_1703_; lean_object* v_nextMacroScope_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1701_ = lean_st_ref_get(v___y_1672_);
v_maxRecDepth_1702_ = lean_ctor_get(v___x_1701_, 5);
lean_inc(v_maxRecDepth_1702_);
lean_dec(v___x_1701_);
v___x_1703_ = lean_st_ref_get(v___y_1672_);
v_nextMacroScope_1704_ = lean_ctor_get(v___x_1703_, 4);
lean_inc(v_nextMacroScope_1704_);
lean_dec(v___x_1703_);
lean_inc(v_currRecDepth_1697_);
v___x_1705_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1705_, 0, v_methods_1692_);
lean_ctor_set(v___x_1705_, 1, v_a_1700_);
lean_ctor_set(v___x_1705_, 2, v_a_1696_);
lean_ctor_set(v___x_1705_, 3, v_currRecDepth_1697_);
lean_ctor_set(v___x_1705_, 4, v_maxRecDepth_1702_);
lean_ctor_set(v___x_1705_, 5, v_a_1694_);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1707_, 0, v_nextMacroScope_1704_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
lean_ctor_set(v___x_1707_, 2, v___x_1706_);
v___x_1708_ = lean_apply_2(v_x_1670_, v___x_1705_, v___x_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_a_1710_; lean_object* v_macroScope_1711_; lean_object* v_traceMsgs_1712_; lean_object* v_expandedMacroDecls_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 1);
lean_inc(v_a_1709_);
v_a_1710_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1708_, 2);
v_macroScope_1711_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_macroScope_1711_);
v_traceMsgs_1712_ = lean_ctor_get(v_a_1709_, 1);
lean_inc(v_traceMsgs_1712_);
v_expandedMacroDecls_1713_ = lean_ctor_get(v_a_1709_, 2);
lean_inc(v_expandedMacroDecls_1713_);
lean_dec(v_a_1709_);
v___x_1714_ = lean_box(0);
v___x_1715_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1713_, v___x_1714_, v___y_1671_, v___y_1672_);
lean_dec(v_expandedMacroDecls_1713_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; lean_object* v_env_1717_; lean_object* v_messages_1718_; lean_object* v_scopes_1719_; lean_object* v_usedQuotCtxts_1720_; lean_object* v_maxRecDepth_1721_; lean_object* v_ngen_1722_; lean_object* v_auxDeclNGen_1723_; lean_object* v_infoState_1724_; lean_object* v_traceState_1725_; lean_object* v_snapshotTasks_1726_; lean_object* v_prevLinterStates_1727_; lean_object* v_codeQualityEntryTasks_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = lean_st_ref_take(v___y_1672_);
v_env_1717_ = lean_ctor_get(v___x_1716_, 0);
v_messages_1718_ = lean_ctor_get(v___x_1716_, 1);
v_scopes_1719_ = lean_ctor_get(v___x_1716_, 2);
v_usedQuotCtxts_1720_ = lean_ctor_get(v___x_1716_, 3);
v_maxRecDepth_1721_ = lean_ctor_get(v___x_1716_, 5);
v_ngen_1722_ = lean_ctor_get(v___x_1716_, 6);
v_auxDeclNGen_1723_ = lean_ctor_get(v___x_1716_, 7);
v_infoState_1724_ = lean_ctor_get(v___x_1716_, 8);
v_traceState_1725_ = lean_ctor_get(v___x_1716_, 9);
v_snapshotTasks_1726_ = lean_ctor_get(v___x_1716_, 10);
v_prevLinterStates_1727_ = lean_ctor_get(v___x_1716_, 11);
v_codeQualityEntryTasks_1728_ = lean_ctor_get(v___x_1716_, 12);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1716_, 4);
lean_dec(v_unused_1755_);
v___x_1730_ = v___x_1716_;
v_isShared_1731_ = v_isSharedCheck_1754_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1728_);
lean_inc(v_prevLinterStates_1727_);
lean_inc(v_snapshotTasks_1726_);
lean_inc(v_traceState_1725_);
lean_inc(v_infoState_1724_);
lean_inc(v_auxDeclNGen_1723_);
lean_inc(v_ngen_1722_);
lean_inc(v_maxRecDepth_1721_);
lean_inc(v_usedQuotCtxts_1720_);
lean_inc(v_scopes_1719_);
lean_inc(v_messages_1718_);
lean_inc(v_env_1717_);
lean_dec(v___x_1716_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1754_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 4, v_macroScope_1711_);
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_env_1717_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_messages_1718_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_scopes_1719_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_usedQuotCtxts_1720_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_macroScope_1711_);
lean_ctor_set(v_reuseFailAlloc_1753_, 5, v_maxRecDepth_1721_);
lean_ctor_set(v_reuseFailAlloc_1753_, 6, v_ngen_1722_);
lean_ctor_set(v_reuseFailAlloc_1753_, 7, v_auxDeclNGen_1723_);
lean_ctor_set(v_reuseFailAlloc_1753_, 8, v_infoState_1724_);
lean_ctor_set(v_reuseFailAlloc_1753_, 9, v_traceState_1725_);
lean_ctor_set(v_reuseFailAlloc_1753_, 10, v_snapshotTasks_1726_);
lean_ctor_set(v_reuseFailAlloc_1753_, 11, v_prevLinterStates_1727_);
lean_ctor_set(v_reuseFailAlloc_1753_, 12, v_codeQualityEntryTasks_1728_);
v___x_1733_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_st_ref_put(v___y_1672_, v___x_1733_);
v___x_1735_ = l_List_reverse___redArg(v_traceMsgs_1712_);
v___x_1736_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1735_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v___x_1736_, 0);
lean_dec(v_unused_1744_);
v___x_1738_ = v___x_1736_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v___x_1736_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v_a_1710_);
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1710_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1710_);
v_a_1745_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1736_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1736_);
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
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_traceMsgs_1712_);
lean_dec(v_macroScope_1711_);
lean_dec(v_a_1710_);
v_a_1756_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1715_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1715_);
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
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1708_, 2);
if (lean_obj_tag(v_a_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_a_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_a_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_a_1765_);
v_a_1766_ = lean_ctor_get(v_a_1764_, 1);
lean_inc_ref(v_a_1766_);
lean_dec_ref_known(v_a_1764_, 2);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1768_ = lean_string_dec_eq(v_a_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1766_);
v___x_1770_ = l_Lean_MessageData_ofFormat(v___x_1769_);
v___x_1771_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1765_, v___x_1770_, v___y_1671_, v___y_1672_);
lean_dec(v_a_1765_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; 
lean_dec_ref(v_a_1766_);
v___x_1772_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1765_);
return v___x_1772_;
}
}
else
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_a_1694_);
lean_dec_ref_known(v_methods_1692_, 5);
lean_dec_ref(v_x_1670_);
v_a_1777_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1695_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1695_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref_known(v_methods_1692_, 5);
lean_dec_ref(v_x_1670_);
v_a_1785_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1693_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1693_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v___f_1686_);
lean_dec(v_currNamespace_1685_);
lean_dec_ref(v_opts_1682_);
lean_dec_ref(v___f_1677_);
lean_dec_ref(v___f_1676_);
lean_dec_ref(v_env_1675_);
lean_dec_ref(v_x_1670_);
v_a_1793_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1687_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1687_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_opts_1682_);
lean_dec_ref(v___f_1677_);
lean_dec_ref(v___f_1676_);
lean_dec_ref(v_env_1675_);
lean_dec_ref(v_x_1670_);
v_a_1801_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1683_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1683_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1670_ = stack[0].m_obj;
lean_object* v___y_1671_ = stack[1].m_obj;
lean_object* v___y_1672_ = stack[2].m_obj;
lean_object* v_res_1809_;
v_res_1809_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1670_, v___y_1671_, v___y_1672_);
stack->m_obj
 = v_res_1809_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1814_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1829_ = l_String_toRawSubstring_x27(v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1853_ = lean_unsigned_to_nat(14u);
v___x_1854_ = lean_unsigned_to_nat(22u);
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1857_ = l_mkPanicMessageWithDecl(v___x_1856_, v___x_1855_, v___x_1854_, v___x_1853_, v___x_1852_);
return v___x_1857_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1874_ = l_String_toRawSubstring_x27(v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1887_ = l_Lean_mkAtom(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1890_ = l_Lean_mkAtom(v___x_1889_);
return v___x_1890_;
}
}
lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1891_, lean_object* v_id_1892_, lean_object* v_stx_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_pat_1898_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1893_);
v___x_1902_ = l_Lean_Syntax_isOfKind(v_stx_1893_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1893_);
v___x_1904_ = l_Lean_Syntax_isOfKind(v_stx_1893_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_a_1911_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v_a_1945_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v_a_1979_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v_a_2015_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v_a_2049_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v_a_2083_; uint8_t v___x_2114_; 
v___x_1905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1893_);
v___x_2114_ = l_Lean_Syntax_isOfKind(v_stx_1893_, v___x_1905_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1893_);
v___x_2116_ = l_Lean_Syntax_isOfKind(v_stx_1893_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1893_);
v___x_2118_ = l_Lean_Syntax_isOfKind(v_stx_1893_, v___x_2117_);
if (v___x_2118_ == 0)
{
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = l_Lean_SourceInfo_fromRef(v_a_2120_, v___x_2118_);
lean_dec(v_a_2120_);
v___x_2122_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_a_2125_; lean_object* v_quotContext_x3f_2156_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v_quotContext_x3f_2156_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2156_) == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v_a_2125_ = v_a_2158_;
goto v___jp_2124_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2123_);
lean_dec(v___x_2121_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2159_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2157_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2157_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_val_2167_; 
v_val_2167_ = lean_ctor_get(v_quotContext_x3f_2156_, 0);
lean_inc(v_val_2167_);
v_a_2125_ = v_val_2167_;
goto v___jp_2124_;
}
v___jp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2126_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2128_ = l_Lean_addMacroScope(v_a_2125_, v___x_2127_, v_a_2123_);
v___x_2129_ = lean_box(0);
lean_inc_n(v___x_2121_, 4);
v___x_2130_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2121_);
lean_ctor_set(v___x_2130_, 1, v___x_2126_);
lean_ctor_set(v___x_2130_, 2, v___x_2128_);
lean_ctor_set(v___x_2130_, 3, v___x_2129_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2121_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2134_ = l_Lean_Syntax_node1(v___x_2121_, v___x_2133_, v_stx_1893_);
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2121_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_node4(v___x_2121_, v___x_1905_, v___x_2130_, v___x_2132_, v___x_2134_, v___x_2136_);
v___x_2138_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2147_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2137_);
lean_ctor_set(v___x_2143_, 1, v_a_2139_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2143_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v___x_2137_);
v_a_2148_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2138_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2138_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v___x_2121_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2168_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2122_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2122_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2176_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2119_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2119_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2185_; 
lean_dec(v_id_1892_);
v_val_2184_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2185_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2184_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v_pat_1898_ = v_a_2186_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_stx_1893_);
v_a_2187_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2185_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2185_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2195_);
lean_inc(v___x_2196_);
v___x_2197_ = l_Lean_Syntax_matchesNull(v___x_2196_, v___x_2195_);
if (v___x_2197_ == 0)
{
lean_dec(v___x_2196_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = l_Lean_SourceInfo_fromRef(v_a_2199_, v___x_2197_);
lean_dec(v_a_2199_);
v___x_2201_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v_a_2204_; lean_object* v_quotContext_x3f_2235_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v_quotContext_x3f_2235_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2235_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v_a_2204_ = v_a_2237_;
goto v___jp_2203_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_a_2202_);
lean_dec(v___x_2200_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2238_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2236_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_val_2246_; 
v_val_2246_ = lean_ctor_get(v_quotContext_x3f_2235_, 0);
lean_inc(v_val_2246_);
v_a_2204_ = v_val_2246_;
goto v___jp_2203_;
}
v___jp_2203_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2205_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2206_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2207_ = l_Lean_addMacroScope(v_a_2204_, v___x_2206_, v_a_2202_);
v___x_2208_ = lean_box(0);
lean_inc_n(v___x_2200_, 4);
v___x_2209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2200_);
lean_ctor_set(v___x_2209_, 1, v___x_2205_);
lean_ctor_set(v___x_2209_, 2, v___x_2207_);
lean_ctor_set(v___x_2209_, 3, v___x_2208_);
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2200_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2213_ = l_Lean_Syntax_node1(v___x_2200_, v___x_2212_, v_stx_1893_);
v___x_2214_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2200_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_Syntax_node4(v___x_2200_, v___x_1905_, v___x_2209_, v___x_2211_, v___x_2213_, v___x_2215_);
v___x_2217_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2226_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2216_);
lean_ctor_set(v___x_2222_, 1, v_a_2218_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2222_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v___x_2216_);
v_a_2227_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2217_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2217_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v___x_2200_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2247_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2201_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2201_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2255_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2198_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2198_);
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
else
{
lean_object* v_val_2263_; lean_object* v___x_2264_; 
lean_dec(v_id_1892_);
v_val_2263_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2264_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2263_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v_pat_1898_ = v_a_2265_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_stx_1893_);
v_a_2266_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2264_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2264_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
else
{
lean_object* v___x_2274_; lean_object* v_stx_2275_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2305_; lean_object* v___y_2306_; 
v___x_2274_ = lean_unsigned_to_nat(0u);
v_stx_2275_ = l_Lean_Syntax_getArg(v___x_2196_, v___x_2274_);
lean_dec(v___x_2196_);
v___x_2293_ = lean_unsigned_to_nat(2u);
v___x_2294_ = lean_unsigned_to_nat(3u);
v___x_2295_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2294_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2295_);
v___x_2454_ = l_Lean_Syntax_isOfKind(v___x_2295_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_dec(v___x_2295_);
lean_dec(v_stx_2275_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = l_Lean_SourceInfo_fromRef(v_a_2456_, v___x_2116_);
lean_dec(v_a_2456_);
v___x_2458_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v_a_2461_; lean_object* v_quotContext_x3f_2492_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v_quotContext_x3f_2492_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2492_) == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v_a_2461_ = v_a_2494_;
goto v___jp_2460_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_a_2459_);
lean_dec(v___x_2457_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2495_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2493_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_val_2503_; 
v_val_2503_ = lean_ctor_get(v_quotContext_x3f_2492_, 0);
lean_inc(v_val_2503_);
v_a_2461_ = v_val_2503_;
goto v___jp_2460_;
}
v___jp_2460_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2462_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2463_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2464_ = l_Lean_addMacroScope(v_a_2461_, v___x_2463_, v_a_2459_);
v___x_2465_ = lean_box(0);
lean_inc_n(v___x_2457_, 4);
v___x_2466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2457_);
lean_ctor_set(v___x_2466_, 1, v___x_2462_);
lean_ctor_set(v___x_2466_, 2, v___x_2464_);
lean_ctor_set(v___x_2466_, 3, v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2457_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2470_ = l_Lean_Syntax_node1(v___x_2457_, v___x_2469_, v_stx_1893_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2457_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Lean_Syntax_node4(v___x_2457_, v___x_1905_, v___x_2466_, v___x_2468_, v___x_2470_, v___x_2472_);
v___x_2474_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2483_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2483_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2483_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2473_);
lean_ctor_set(v___x_2479_, 1, v_a_2475_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2479_);
v___x_2481_ = v___x_2477_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v___x_2473_);
v_a_2484_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2474_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2474_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v___x_2457_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2504_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2458_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2458_);
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
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2512_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2455_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2455_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2521_; 
lean_dec(v_id_1892_);
v_val_2520_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2520_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2521_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2520_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v_pat_1898_ = v_a_2522_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_stx_1893_);
v_a_2523_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2521_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2521_);
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
}
else
{
goto v___jp_2356_;
}
}
else
{
goto v___jp_2356_;
}
v___jp_2276_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2282_ = lean_string_append(v___y_2280_, v___x_2281_);
lean_inc(v___y_2277_);
v___x_2283_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2277_, v_stx_2275_, v_id_1892_, v___x_2282_, v___y_2279_, v___y_2278_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v_pat_1898_ = v_a_2284_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_stx_1893_);
v_a_2285_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
v___jp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2300_ = l_Lean_Syntax_isStrLit_x3f(v___x_2295_);
lean_dec(v___x_2295_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2302_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2301_);
v___y_2277_ = v___x_2299_;
v___y_2278_ = v___y_2298_;
v___y_2279_ = v___y_2297_;
v___y_2280_ = v___x_2302_;
goto v___jp_2276_;
}
else
{
lean_object* v_val_2303_; 
v_val_2303_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v___x_2300_, 1);
v___y_2277_ = v___x_2299_;
v___y_2278_ = v___y_2298_;
v___y_2279_ = v___y_2297_;
v___y_2280_ = v_val_2303_;
goto v___jp_2276_;
}
}
v___jp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = lean_unsigned_to_nat(5u);
v___x_2308_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2307_);
v___x_2309_ = l_Lean_Syntax_isNone(v___x_2308_);
if (v___x_2309_ == 0)
{
uint8_t v___x_2310_; 
v___x_2310_ = l_Lean_Syntax_matchesNull(v___x_2308_, v___x_2293_);
if (v___x_2310_ == 0)
{
lean_dec(v___x_2295_);
lean_dec(v_stx_2275_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Elab_Command_getRef___redArg(v___y_2305_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l_Lean_SourceInfo_fromRef(v_a_2312_, v___x_2310_);
lean_dec(v_a_2312_);
v___x_2314_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2305_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_quotContext_x3f_2315_; 
v_quotContext_x3f_2315_ = lean_ctor_get(v___y_2305_, 5);
if (lean_obj_tag(v_quotContext_x3f_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2317_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2306_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___y_1907_ = v_a_2316_;
v___y_1908_ = v___x_2313_;
v___y_1909_ = v___y_2306_;
v___y_1910_ = v___y_2305_;
v_a_1911_ = v_a_2318_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_a_2316_);
lean_dec(v___x_2313_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2319_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2317_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2317_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v_val_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2314_, 1);
v_val_2328_ = lean_ctor_get(v_quotContext_x3f_2315_, 0);
lean_inc(v_val_2328_);
v___y_1907_ = v_a_2327_;
v___y_1908_ = v___x_2313_;
v___y_1909_ = v___y_2306_;
v___y_1910_ = v___y_2305_;
v_a_1911_ = v_val_2328_;
goto v___jp_1906_;
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v___x_2313_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2329_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2314_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2314_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2337_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2311_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2311_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v_val_2345_; lean_object* v___x_2346_; 
lean_dec(v_id_1892_);
v_val_2345_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2346_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2345_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v_pat_1898_ = v_a_2347_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_stx_1893_);
v_a_2348_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2346_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2346_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1891_);
v___y_2297_ = v___y_2305_;
v___y_2298_ = v___y_2306_;
goto v___jp_2296_;
}
}
else
{
lean_dec(v___x_2308_);
lean_dec(v_id_x3f_1891_);
v___y_2297_ = v___y_2305_;
v___y_2298_ = v___y_2306_;
goto v___jp_2296_;
}
}
v___jp_2356_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2357_ = lean_unsigned_to_nat(4u);
v___x_2358_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2357_);
v___x_2359_ = l_Lean_Syntax_isNone(v___x_2358_);
if (v___x_2359_ == 0)
{
uint8_t v___x_2360_; 
lean_inc(v___x_2358_);
v___x_2360_ = l_Lean_Syntax_matchesNull(v___x_2358_, v___x_2293_);
if (v___x_2360_ == 0)
{
lean_dec(v___x_2358_);
lean_dec(v___x_2295_);
lean_dec(v_stx_2275_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_SourceInfo_fromRef(v_a_2362_, v___x_2360_);
lean_dec(v_a_2362_);
v___x_2364_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_quotContext_x3f_2365_; 
v_quotContext_x3f_2365_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; 
v_a_2366_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2367_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v___y_1943_ = v_a_2366_;
v___y_1944_ = v___x_2363_;
v_a_1945_ = v_a_2368_;
goto v___jp_1942_;
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2366_);
lean_dec(v___x_2363_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2369_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2367_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2367_);
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
lean_object* v_a_2377_; lean_object* v_val_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2364_, 1);
v_val_2378_ = lean_ctor_get(v_quotContext_x3f_2365_, 0);
lean_inc(v_val_2378_);
v___y_1943_ = v_a_2377_;
v___y_1944_ = v___x_2363_;
v_a_1945_ = v_val_2378_;
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v___x_2363_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2379_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2364_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2364_);
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
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2387_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2361_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2361_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_val_2395_; lean_object* v___x_2396_; 
lean_dec(v_id_1892_);
v_val_2395_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2396_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2395_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v_pat_1898_ = v_a_2397_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v_stx_1893_);
v_a_2398_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2396_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
else
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = l_Lean_Syntax_getArg(v___x_2358_, v___x_2195_);
lean_dec(v___x_2358_);
v___x_2407_ = l_Lean_Syntax_matchesNull(v___x_2406_, v___x_2195_);
if (v___x_2407_ == 0)
{
lean_dec(v___x_2295_);
lean_dec(v_stx_2275_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = l_Lean_SourceInfo_fromRef(v_a_2409_, v___x_2407_);
lean_dec(v_a_2409_);
v___x_2411_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_quotContext_x3f_2412_; 
v_quotContext_x3f_2412_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2414_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___y_1977_ = v___x_2410_;
v___y_1978_ = v_a_2413_;
v_a_1979_ = v_a_2415_;
goto v___jp_1976_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_a_2413_);
lean_dec(v___x_2410_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2416_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2414_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v_val_2425_; 
v_a_2424_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2411_, 1);
v_val_2425_ = lean_ctor_get(v_quotContext_x3f_2412_, 0);
lean_inc(v_val_2425_);
v___y_1977_ = v___x_2410_;
v___y_1978_ = v_a_2424_;
v_a_1979_ = v_val_2425_;
goto v___jp_1976_;
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v___x_2410_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2426_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2411_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2411_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2434_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2408_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2408_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_val_2442_; lean_object* v___x_2443_; 
lean_dec(v_id_1892_);
v_val_2442_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2442_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2443_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2442_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v_pat_1898_ = v_a_2444_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_stx_1893_);
v_a_2445_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2443_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2443_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
else
{
v___y_2305_ = v_a_1894_;
v___y_2306_ = v_a_1895_;
goto v___jp_2304_;
}
}
}
else
{
lean_dec(v___x_2358_);
v___y_2305_ = v_a_1894_;
v___y_2306_ = v_a_1895_;
goto v___jp_2304_;
}
}
}
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2531_);
lean_inc(v___x_2532_);
v___x_2533_ = l_Lean_Syntax_matchesNull(v___x_2532_, v___x_2531_);
if (v___x_2533_ == 0)
{
lean_dec(v___x_2532_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = l_Lean_SourceInfo_fromRef(v_a_2535_, v___x_2533_);
lean_dec(v_a_2535_);
v___x_2537_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v_a_2540_; lean_object* v_quotContext_x3f_2571_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v_quotContext_x3f_2571_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2571_) == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v_a_2540_ = v_a_2573_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_a_2538_);
lean_dec(v___x_2536_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2574_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2572_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_val_2582_; 
v_val_2582_ = lean_ctor_get(v_quotContext_x3f_2571_, 0);
lean_inc(v_val_2582_);
v_a_2540_ = v_val_2582_;
goto v___jp_2539_;
}
v___jp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2541_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2542_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2543_ = l_Lean_addMacroScope(v_a_2540_, v___x_2542_, v_a_2538_);
v___x_2544_ = lean_box(0);
lean_inc_n(v___x_2536_, 4);
v___x_2545_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2536_);
lean_ctor_set(v___x_2545_, 1, v___x_2541_);
lean_ctor_set(v___x_2545_, 2, v___x_2543_);
lean_ctor_set(v___x_2545_, 3, v___x_2544_);
v___x_2546_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2536_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2549_ = l_Lean_Syntax_node1(v___x_2536_, v___x_2548_, v_stx_1893_);
v___x_2550_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2536_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node4(v___x_2536_, v___x_1905_, v___x_2545_, v___x_2547_, v___x_2549_, v___x_2551_);
v___x_2553_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2562_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2552_);
lean_ctor_set(v___x_2558_, 1, v_a_2554_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2558_);
v___x_2560_ = v___x_2556_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v___x_2552_);
v_a_2563_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2553_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2553_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v___x_2536_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2583_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2537_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2537_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2591_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2534_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2534_);
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
else
{
lean_object* v_val_2599_; lean_object* v___x_2600_; 
lean_dec(v_id_1892_);
v_val_2599_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2600_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2599_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v_pat_1898_ = v_a_2601_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_stx_1893_);
v_a_2602_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2600_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
else
{
lean_object* v___x_2610_; lean_object* v_stx_2611_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2641_; lean_object* v___y_2642_; 
v___x_2610_ = lean_unsigned_to_nat(0u);
v_stx_2611_ = l_Lean_Syntax_getArg(v___x_2532_, v___x_2610_);
lean_dec(v___x_2532_);
v___x_2629_ = lean_unsigned_to_nat(2u);
v___x_2630_ = lean_unsigned_to_nat(3u);
v___x_2631_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2630_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2631_);
v___x_2790_ = l_Lean_Syntax_isOfKind(v___x_2631_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_dec(v___x_2631_);
lean_dec(v_stx_2611_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_SourceInfo_fromRef(v_a_2792_, v___x_2114_);
lean_dec(v_a_2792_);
v___x_2794_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v_a_2797_; lean_object* v_quotContext_x3f_2828_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v_quotContext_x3f_2828_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2828_) == 0)
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v_a_2797_ = v_a_2830_;
goto v___jp_2796_;
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_a_2795_);
lean_dec(v___x_2793_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2831_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2829_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2829_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_val_2839_; 
v_val_2839_ = lean_ctor_get(v_quotContext_x3f_2828_, 0);
lean_inc(v_val_2839_);
v_a_2797_ = v_val_2839_;
goto v___jp_2796_;
}
v___jp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2798_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2799_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2800_ = l_Lean_addMacroScope(v_a_2797_, v___x_2799_, v_a_2795_);
v___x_2801_ = lean_box(0);
lean_inc_n(v___x_2793_, 4);
v___x_2802_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2793_);
lean_ctor_set(v___x_2802_, 1, v___x_2798_);
lean_ctor_set(v___x_2802_, 2, v___x_2800_);
lean_ctor_set(v___x_2802_, 3, v___x_2801_);
v___x_2803_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2793_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2806_ = l_Lean_Syntax_node1(v___x_2793_, v___x_2805_, v_stx_1893_);
v___x_2807_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2793_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_Syntax_node4(v___x_2793_, v___x_1905_, v___x_2802_, v___x_2804_, v___x_2806_, v___x_2808_);
v___x_2810_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2809_);
lean_ctor_set(v___x_2815_, 1, v_a_2811_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v___x_2809_);
v_a_2820_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2810_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2810_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___x_2793_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2840_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2794_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2794_);
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
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2848_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2791_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2791_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_val_2856_; lean_object* v___x_2857_; 
lean_dec(v_id_1892_);
v_val_2856_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2856_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2857_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2856_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_pat_1898_ = v_a_2858_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_stx_1893_);
v_a_2859_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2857_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2857_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
else
{
goto v___jp_2692_;
}
}
else
{
goto v___jp_2692_;
}
v___jp_2612_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2618_ = lean_string_append(v___y_2616_, v___x_2617_);
lean_inc(v___y_2614_);
v___x_2619_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2614_, v_stx_2611_, v_id_1892_, v___x_2618_, v___y_2613_, v___y_2615_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v_pat_1898_ = v_a_2620_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_stx_1893_);
v_a_2621_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2619_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2619_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
v___jp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2636_ = l_Lean_Syntax_isStrLit_x3f(v___x_2631_);
lean_dec(v___x_2631_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2638_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2637_);
v___y_2613_ = v___y_2633_;
v___y_2614_ = v___x_2635_;
v___y_2615_ = v___y_2634_;
v___y_2616_ = v___x_2638_;
goto v___jp_2612_;
}
else
{
lean_object* v_val_2639_; 
v_val_2639_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v___x_2636_, 1);
v___y_2613_ = v___y_2633_;
v___y_2614_ = v___x_2635_;
v___y_2615_ = v___y_2634_;
v___y_2616_ = v_val_2639_;
goto v___jp_2612_;
}
}
v___jp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = lean_unsigned_to_nat(5u);
v___x_2644_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2643_);
v___x_2645_ = l_Lean_Syntax_isNone(v___x_2644_);
if (v___x_2645_ == 0)
{
uint8_t v___x_2646_; 
v___x_2646_ = l_Lean_Syntax_matchesNull(v___x_2644_, v___x_2629_);
if (v___x_2646_ == 0)
{
lean_dec(v___x_2631_);
lean_dec(v_stx_2611_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Elab_Command_getRef___redArg(v___y_2641_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = l_Lean_SourceInfo_fromRef(v_a_2648_, v___x_2646_);
lean_dec(v_a_2648_);
v___x_2650_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2641_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_quotContext_x3f_2651_; 
v_quotContext_x3f_2651_ = lean_ctor_get(v___y_2641_, 5);
if (lean_obj_tag(v_quotContext_x3f_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2653_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2642_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___y_2011_ = v___y_2641_;
v___y_2012_ = v_a_2652_;
v___y_2013_ = v___y_2642_;
v___y_2014_ = v___x_2649_;
v_a_2015_ = v_a_2654_;
goto v___jp_2010_;
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_a_2652_);
lean_dec(v___x_2649_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2655_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2653_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2653_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v_val_2664_; 
v_a_2663_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2650_, 1);
v_val_2664_ = lean_ctor_get(v_quotContext_x3f_2651_, 0);
lean_inc(v_val_2664_);
v___y_2011_ = v___y_2641_;
v___y_2012_ = v_a_2663_;
v___y_2013_ = v___y_2642_;
v___y_2014_ = v___x_2649_;
v_a_2015_ = v_val_2664_;
goto v___jp_2010_;
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v___x_2649_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2665_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2650_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2650_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2673_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2647_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2647_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_val_2681_; lean_object* v___x_2682_; 
lean_dec(v_id_1892_);
v_val_2681_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2681_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2682_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2681_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v_pat_1898_ = v_a_2683_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_stx_1893_);
v_a_2684_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2682_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2682_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1891_);
v___y_2633_ = v___y_2641_;
v___y_2634_ = v___y_2642_;
goto v___jp_2632_;
}
}
else
{
lean_dec(v___x_2644_);
lean_dec(v_id_x3f_1891_);
v___y_2633_ = v___y_2641_;
v___y_2634_ = v___y_2642_;
goto v___jp_2632_;
}
}
v___jp_2692_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2693_ = lean_unsigned_to_nat(4u);
v___x_2694_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2693_);
v___x_2695_ = l_Lean_Syntax_isNone(v___x_2694_);
if (v___x_2695_ == 0)
{
uint8_t v___x_2696_; 
lean_inc(v___x_2694_);
v___x_2696_ = l_Lean_Syntax_matchesNull(v___x_2694_, v___x_2629_);
if (v___x_2696_ == 0)
{
lean_dec(v___x_2694_);
lean_dec(v___x_2631_);
lean_dec(v_stx_2611_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l_Lean_SourceInfo_fromRef(v_a_2698_, v___x_2696_);
lean_dec(v_a_2698_);
v___x_2700_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_quotContext_x3f_2701_; 
v_quotContext_x3f_2701_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2703_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___y_2047_ = v_a_2702_;
v___y_2048_ = v___x_2699_;
v_a_2049_ = v_a_2704_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_a_2702_);
lean_dec(v___x_2699_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
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
else
{
lean_object* v_a_2713_; lean_object* v_val_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2700_, 1);
v_val_2714_ = lean_ctor_get(v_quotContext_x3f_2701_, 0);
lean_inc(v_val_2714_);
v___y_2047_ = v_a_2713_;
v___y_2048_ = v___x_2699_;
v_a_2049_ = v_val_2714_;
goto v___jp_2046_;
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v___x_2699_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2715_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2700_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2700_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2723_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2697_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2697_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_val_2731_; lean_object* v___x_2732_; 
lean_dec(v_id_1892_);
v_val_2731_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2731_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2732_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2731_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v_pat_1898_ = v_a_2733_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_stx_1893_);
v_a_2734_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2732_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2732_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
else
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = l_Lean_Syntax_getArg(v___x_2694_, v___x_2531_);
lean_dec(v___x_2694_);
v___x_2743_ = l_Lean_Syntax_matchesNull(v___x_2742_, v___x_2531_);
if (v___x_2743_ == 0)
{
lean_dec(v___x_2631_);
lean_dec(v_stx_2611_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l_Lean_SourceInfo_fromRef(v_a_2745_, v___x_2743_);
lean_dec(v_a_2745_);
v___x_2747_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_quotContext_x3f_2748_; 
v_quotContext_x3f_2748_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2750_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___y_2081_ = v_a_2749_;
v___y_2082_ = v___x_2746_;
v_a_2083_ = v_a_2751_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2749_);
lean_dec(v___x_2746_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2752_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2750_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v_val_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2747_, 1);
v_val_2761_ = lean_ctor_get(v_quotContext_x3f_2748_, 0);
lean_inc(v_val_2761_);
v___y_2081_ = v_a_2760_;
v___y_2082_ = v___x_2746_;
v_a_2083_ = v_val_2761_;
goto v___jp_2080_;
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v___x_2746_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2762_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2747_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2747_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2770_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2744_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2744_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_val_2778_; lean_object* v___x_2779_; 
lean_dec(v_id_1892_);
v_val_2778_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2778_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2779_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2778_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v_pat_1898_ = v_a_2780_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_stx_1893_);
v_a_2781_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2779_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2779_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
else
{
v___y_2641_ = v_a_1894_;
v___y_2642_ = v_a_1895_;
goto v___jp_2640_;
}
}
}
else
{
lean_dec(v___x_2694_);
v___y_2641_ = v_a_1894_;
v___y_2642_ = v_a_1895_;
goto v___jp_2640_;
}
}
}
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2867_);
v___x_2869_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2870_ = l_Lean_Syntax_matchesIdent(v___x_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2872_ = l_Lean_Syntax_matchesIdent(v___x_2868_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2874_ = l_Lean_Syntax_matchesIdent(v___x_2868_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2876_ = l_Lean_Syntax_matchesIdent(v___x_2868_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2878_ = l_Lean_Syntax_matchesIdent(v___x_2868_, v___x_2877_);
lean_dec(v___x_2868_);
if (v___x_2878_ == 0)
{
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = l_Lean_SourceInfo_fromRef(v_a_2880_, v___x_2878_);
lean_dec(v_a_2880_);
v___x_2882_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_a_2885_; lean_object* v_quotContext_x3f_2916_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v_quotContext_x3f_2916_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2916_) == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v_a_2885_ = v_a_2918_;
goto v___jp_2884_;
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_a_2883_);
lean_dec(v___x_2881_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
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
v_val_2927_ = lean_ctor_get(v_quotContext_x3f_2916_, 0);
lean_inc(v_val_2927_);
v_a_2885_ = v_val_2927_;
goto v___jp_2884_;
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2886_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2887_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2888_ = l_Lean_addMacroScope(v_a_2885_, v___x_2887_, v_a_2883_);
v___x_2889_ = lean_box(0);
lean_inc_n(v___x_2881_, 4);
v___x_2890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2881_);
lean_ctor_set(v___x_2890_, 1, v___x_2886_);
lean_ctor_set(v___x_2890_, 2, v___x_2888_);
lean_ctor_set(v___x_2890_, 3, v___x_2889_);
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2881_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2894_ = l_Lean_Syntax_node1(v___x_2881_, v___x_2893_, v_stx_1893_);
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2881_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = l_Lean_Syntax_node4(v___x_2881_, v___x_1905_, v___x_2890_, v___x_2892_, v___x_2894_, v___x_2896_);
v___x_2898_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2907_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2897_);
lean_ctor_set(v___x_2903_, 1, v_a_2899_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2903_);
v___x_2905_ = v___x_2901_;
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
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v___x_2897_);
v_a_2908_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2898_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2898_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v___x_2881_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2928_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2882_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2882_);
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
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2936_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2879_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2879_);
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
lean_object* v_val_2944_; lean_object* v___x_2945_; 
lean_dec(v_id_1892_);
v_val_2944_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_2944_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_2945_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_2944_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v_pat_1898_ = v_a_2946_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_stx_1893_);
v_a_2947_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2945_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2945_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2955_ = lean_unsigned_to_nat(1u);
v___x_2956_ = lean_unsigned_to_nat(2u);
v___x_2957_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_2956_);
lean_inc(v___x_2957_);
v___x_2958_ = l_Lean_Syntax_matchesNull(v___x_2957_, v___x_2955_);
if (v___x_2958_ == 0)
{
lean_dec(v___x_2957_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2961_ = l_Lean_SourceInfo_fromRef(v_a_2960_, v___x_2958_);
lean_dec(v_a_2960_);
v___x_2962_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v_a_2965_; lean_object* v_quotContext_x3f_2996_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v_quotContext_x3f_2996_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_2996_) == 0)
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v_a_2965_ = v_a_2998_;
goto v___jp_2964_;
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2963_);
lean_dec(v___x_2961_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_2999_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2997_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2997_);
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
lean_object* v_val_3007_; 
v_val_3007_ = lean_ctor_get(v_quotContext_x3f_2996_, 0);
lean_inc(v_val_3007_);
v_a_2965_ = v_val_3007_;
goto v___jp_2964_;
}
v___jp_2964_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2966_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2967_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2968_ = l_Lean_addMacroScope(v_a_2965_, v___x_2967_, v_a_2963_);
v___x_2969_ = lean_box(0);
lean_inc_n(v___x_2961_, 4);
v___x_2970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2961_);
lean_ctor_set(v___x_2970_, 1, v___x_2966_);
lean_ctor_set(v___x_2970_, 2, v___x_2968_);
lean_ctor_set(v___x_2970_, 3, v___x_2969_);
v___x_2971_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2961_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2974_ = l_Lean_Syntax_node1(v___x_2961_, v___x_2973_, v_stx_1893_);
v___x_2975_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2961_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l_Lean_Syntax_node4(v___x_2961_, v___x_1905_, v___x_2970_, v___x_2972_, v___x_2974_, v___x_2976_);
v___x_2978_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2987_; 
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
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
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
lean_dec(v___x_2977_);
v_a_2988_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2978_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2978_);
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
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v___x_2961_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3008_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2962_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2962_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3016_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2959_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2959_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_val_3024_; lean_object* v___x_3025_; 
lean_dec(v_id_1892_);
v_val_3024_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3024_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3025_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3024_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v_pat_1898_ = v_a_3026_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_stx_1893_);
v_a_3027_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3025_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3025_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v_stx_3035_; lean_object* v___x_3036_; 
lean_dec(v_stx_1893_);
v_stx_3035_ = l_Lean_Syntax_getArg(v___x_2957_, v___x_2867_);
lean_dec(v___x_2957_);
v___x_3036_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1891_, v_id_1892_, v_stx_3035_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v_fst_3038_; lean_object* v_snd_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3099_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v___x_3036_, 1);
v_fst_3038_ = lean_ctor_get(v_a_3037_, 0);
v_snd_3039_ = lean_ctor_get(v_a_3037_, 1);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_a_3037_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3041_ = v_a_3037_;
v_isShared_3042_ = v_isSharedCheck_3099_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_snd_3039_);
lean_inc(v_fst_3038_);
lean_dec(v_a_3037_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3099_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v___x_3045_ = l_Lean_SourceInfo_fromRef(v_a_3044_, v___x_2876_);
lean_dec(v_a_3044_);
v___x_3046_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3082_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3082_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3082_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_a_3052_; lean_object* v_quotContext_x3f_3070_; 
v_quotContext_x3f_3070_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3070_) == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v_a_3052_ = v_a_3072_;
goto v___jp_3051_;
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_del_object(v___x_3049_);
lean_dec(v_a_3047_);
lean_dec(v___x_3045_);
lean_del_object(v___x_3041_);
lean_dec(v_snd_3039_);
lean_dec(v_fst_3038_);
v_a_3073_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3071_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3071_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_val_3081_; 
v_val_3081_ = lean_ctor_get(v_quotContext_x3f_3070_, 0);
lean_inc(v_val_3081_);
v_a_3052_ = v_val_3081_;
goto v___jp_3051_;
}
v___jp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3053_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_3054_ = l_Lean_addMacroScope(v_a_3052_, v___x_2877_, v_a_3047_);
v___x_3055_ = lean_box(0);
lean_inc_n(v___x_3045_, 4);
v___x_3056_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3045_);
lean_ctor_set(v___x_3056_, 1, v___x_3053_);
lean_ctor_set(v___x_3056_, 2, v___x_3054_);
lean_ctor_set(v___x_3056_, 3, v___x_3055_);
v___x_3057_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3045_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_3060_ = l_Lean_Syntax_node1(v___x_3045_, v___x_3059_, v_fst_3038_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3045_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = l_Lean_Syntax_node4(v___x_3045_, v___x_1905_, v___x_3056_, v___x_3058_, v___x_3060_, v___x_3062_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3063_);
v___x_3065_ = v___x_3041_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_snd_3039_);
v___x_3065_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3067_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3065_);
v___x_3067_ = v___x_3049_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v___x_3045_);
lean_del_object(v___x_3041_);
lean_dec(v_snd_3039_);
lean_dec(v_fst_3038_);
v_a_3083_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3046_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3046_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_del_object(v___x_3041_);
lean_dec(v_snd_3039_);
lean_dec(v_fst_3038_);
v_a_3091_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3043_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3043_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
else
{
return v___x_3036_;
}
}
}
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
lean_dec(v___x_2868_);
v___x_3100_ = lean_unsigned_to_nat(1u);
v___x_3101_ = lean_unsigned_to_nat(2u);
v___x_3102_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_3101_);
lean_inc(v___x_3102_);
v___x_3103_ = l_Lean_Syntax_matchesNull(v___x_3102_, v___x_3100_);
if (v___x_3103_ == 0)
{
lean_dec(v___x_3102_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = l_Lean_SourceInfo_fromRef(v_a_3105_, v___x_3103_);
lean_dec(v_a_3105_);
v___x_3107_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v_a_3110_; lean_object* v_quotContext_x3f_3141_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v_quotContext_x3f_3141_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3141_) == 0)
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v_a_3110_ = v_a_3143_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3108_);
lean_dec(v___x_3106_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3144_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3142_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_val_3152_; 
v_val_3152_ = lean_ctor_get(v_quotContext_x3f_3141_, 0);
lean_inc(v_val_3152_);
v_a_3110_ = v_val_3152_;
goto v___jp_3109_;
}
v___jp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3111_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3113_ = l_Lean_addMacroScope(v_a_3110_, v___x_3112_, v_a_3108_);
v___x_3114_ = lean_box(0);
lean_inc_n(v___x_3106_, 4);
v___x_3115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3106_);
lean_ctor_set(v___x_3115_, 1, v___x_3111_);
lean_ctor_set(v___x_3115_, 2, v___x_3113_);
lean_ctor_set(v___x_3115_, 3, v___x_3114_);
v___x_3116_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3106_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3119_ = l_Lean_Syntax_node1(v___x_3106_, v___x_3118_, v_stx_1893_);
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3106_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = l_Lean_Syntax_node4(v___x_3106_, v___x_1905_, v___x_3115_, v___x_3117_, v___x_3119_, v___x_3121_);
v___x_3123_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3132_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3122_);
lean_ctor_set(v___x_3128_, 1, v_a_3124_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3128_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v___x_3122_);
v_a_3133_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3123_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3123_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v___x_3106_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3153_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3107_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3107_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3161_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3104_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3104_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_val_3169_; lean_object* v___x_3170_; 
lean_dec(v_id_1892_);
v_val_3169_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3170_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3169_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v_pat_1898_ = v_a_3171_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_stx_1893_);
v_a_3172_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3170_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3170_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3180_ = l_Lean_Syntax_getArg(v___x_3102_, v___x_2867_);
lean_dec(v___x_3102_);
v___x_3181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3180_);
v___x_3182_ = l_Lean_Syntax_isOfKind(v___x_3180_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_dec(v___x_3180_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = l_Lean_SourceInfo_fromRef(v_a_3184_, v___x_3182_);
lean_dec(v_a_3184_);
v___x_3186_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v_a_3189_; lean_object* v_quotContext_x3f_3220_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v_quotContext_x3f_3220_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3220_) == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v_a_3189_ = v_a_3222_;
goto v___jp_3188_;
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec(v_a_3187_);
lean_dec(v___x_3185_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3223_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3221_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3221_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v_val_3231_; 
v_val_3231_ = lean_ctor_get(v_quotContext_x3f_3220_, 0);
lean_inc(v_val_3231_);
v_a_3189_ = v_val_3231_;
goto v___jp_3188_;
}
v___jp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3190_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3191_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3192_ = l_Lean_addMacroScope(v_a_3189_, v___x_3191_, v_a_3187_);
v___x_3193_ = lean_box(0);
lean_inc_n(v___x_3185_, 4);
v___x_3194_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3185_);
lean_ctor_set(v___x_3194_, 1, v___x_3190_);
lean_ctor_set(v___x_3194_, 2, v___x_3192_);
lean_ctor_set(v___x_3194_, 3, v___x_3193_);
v___x_3195_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3185_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3198_ = l_Lean_Syntax_node1(v___x_3185_, v___x_3197_, v_stx_1893_);
v___x_3199_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3185_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_node4(v___x_3185_, v___x_1905_, v___x_3194_, v___x_3196_, v___x_3198_, v___x_3200_);
v___x_3202_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3211_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3211_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3211_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3201_);
lean_ctor_set(v___x_3207_, 1, v_a_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3207_);
v___x_3209_ = v___x_3205_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v___x_3201_);
v_a_3212_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3202_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3202_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v___x_3185_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3232_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3186_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3186_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3240_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3183_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3183_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_val_3248_; lean_object* v___x_3249_; 
lean_dec(v_id_1892_);
v_val_3248_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3248_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3249_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3248_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v_pat_1898_ = v_a_3250_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_stx_1893_);
v_a_3251_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3249_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3259_ = l_Lean_Syntax_getArg(v___x_3180_, v___x_2867_);
v___x_3260_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3261_ = l_Lean_Syntax_matchesIdent(v___x_3259_, v___x_3260_);
lean_dec(v___x_3259_);
if (v___x_3261_ == 0)
{
lean_dec(v___x_3180_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_Lean_SourceInfo_fromRef(v_a_3263_, v___x_3261_);
lean_dec(v_a_3263_);
v___x_3265_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v_a_3268_; lean_object* v_quotContext_x3f_3299_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v_quotContext_x3f_3299_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3299_) == 0)
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v_a_3268_ = v_a_3301_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_a_3266_);
lean_dec(v___x_3264_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3302_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3300_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3300_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_val_3310_; 
v_val_3310_ = lean_ctor_get(v_quotContext_x3f_3299_, 0);
lean_inc(v_val_3310_);
v_a_3268_ = v_val_3310_;
goto v___jp_3267_;
}
v___jp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3269_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3270_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3271_ = l_Lean_addMacroScope(v_a_3268_, v___x_3270_, v_a_3266_);
v___x_3272_ = lean_box(0);
lean_inc_n(v___x_3264_, 4);
v___x_3273_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3264_);
lean_ctor_set(v___x_3273_, 1, v___x_3269_);
lean_ctor_set(v___x_3273_, 2, v___x_3271_);
lean_ctor_set(v___x_3273_, 3, v___x_3272_);
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3264_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3277_ = l_Lean_Syntax_node1(v___x_3264_, v___x_3276_, v_stx_1893_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3264_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = l_Lean_Syntax_node4(v___x_3264_, v___x_1905_, v___x_3273_, v___x_3275_, v___x_3277_, v___x_3279_);
v___x_3281_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3290_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3290_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3290_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3280_);
lean_ctor_set(v___x_3286_, 1, v_a_3282_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3286_);
v___x_3288_ = v___x_3284_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v___x_3280_);
v_a_3291_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3281_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3281_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v___x_3264_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3311_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3265_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3265_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3319_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3262_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3262_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_val_3327_; lean_object* v___x_3328_; 
lean_dec(v_id_1892_);
v_val_3327_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3328_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3327_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v_pat_1898_ = v_a_3329_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec(v_stx_1893_);
v_a_3330_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3328_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3328_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
else
{
lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3338_ = l_Lean_Syntax_getArg(v___x_3180_, v___x_3100_);
lean_dec(v___x_3180_);
v___x_3339_ = l_Lean_Syntax_matchesNull(v___x_3338_, v___x_2867_);
if (v___x_3339_ == 0)
{
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = l_Lean_SourceInfo_fromRef(v_a_3341_, v___x_3339_);
lean_dec(v_a_3341_);
v___x_3343_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v_a_3346_; lean_object* v_quotContext_x3f_3377_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v_quotContext_x3f_3377_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3377_) == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v_a_3346_ = v_a_3379_;
goto v___jp_3345_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec(v_a_3344_);
lean_dec(v___x_3342_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3380_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3378_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3378_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_val_3388_; 
v_val_3388_ = lean_ctor_get(v_quotContext_x3f_3377_, 0);
lean_inc(v_val_3388_);
v_a_3346_ = v_val_3388_;
goto v___jp_3345_;
}
v___jp_3345_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3347_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3349_ = l_Lean_addMacroScope(v_a_3346_, v___x_3348_, v_a_3344_);
v___x_3350_ = lean_box(0);
lean_inc_n(v___x_3342_, 4);
v___x_3351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3342_);
lean_ctor_set(v___x_3351_, 1, v___x_3347_);
lean_ctor_set(v___x_3351_, 2, v___x_3349_);
lean_ctor_set(v___x_3351_, 3, v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3342_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3355_ = l_Lean_Syntax_node1(v___x_3342_, v___x_3354_, v_stx_1893_);
v___x_3356_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3342_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = l_Lean_Syntax_node4(v___x_3342_, v___x_1905_, v___x_3351_, v___x_3353_, v___x_3355_, v___x_3357_);
v___x_3359_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3368_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3368_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3368_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3358_);
lean_ctor_set(v___x_3364_, 1, v_a_3360_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3364_);
v___x_3366_ = v___x_3362_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v___x_3358_);
v_a_3369_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3359_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3359_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v___x_3342_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3389_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3343_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3343_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3397_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3340_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3340_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3406_; 
lean_dec(v_id_1892_);
v_val_3405_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3406_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3405_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v_pat_1898_ = v_a_3407_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v_stx_1893_);
v_a_3408_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3406_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3406_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec(v_id_x3f_1891_);
v___x_3416_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3417_ = lean_box(0);
v___x_3418_ = l_Lean_Syntax_mkAntiquotNode(v___x_3416_, v_id_1892_, v___x_2867_, v___x_3417_, v___x_2874_);
v_pat_1898_ = v___x_3418_;
goto v___jp_1897_;
}
}
}
}
}
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
lean_dec(v___x_2868_);
v___x_3419_ = lean_unsigned_to_nat(1u);
v___x_3420_ = lean_unsigned_to_nat(2u);
v___x_3421_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_3420_);
lean_inc(v___x_3421_);
v___x_3422_ = l_Lean_Syntax_matchesNull(v___x_3421_, v___x_3419_);
if (v___x_3422_ == 0)
{
lean_dec(v___x_3421_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = l_Lean_SourceInfo_fromRef(v_a_3424_, v___x_3422_);
lean_dec(v_a_3424_);
v___x_3426_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v_a_3429_; lean_object* v_quotContext_x3f_3460_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v_quotContext_x3f_3460_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3460_) == 0)
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v_a_3429_ = v_a_3462_;
goto v___jp_3428_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_a_3427_);
lean_dec(v___x_3425_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3463_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3461_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3461_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_val_3471_; 
v_val_3471_ = lean_ctor_get(v_quotContext_x3f_3460_, 0);
lean_inc(v_val_3471_);
v_a_3429_ = v_val_3471_;
goto v___jp_3428_;
}
v___jp_3428_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3430_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3431_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3432_ = l_Lean_addMacroScope(v_a_3429_, v___x_3431_, v_a_3427_);
v___x_3433_ = lean_box(0);
lean_inc_n(v___x_3425_, 4);
v___x_3434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3425_);
lean_ctor_set(v___x_3434_, 1, v___x_3430_);
lean_ctor_set(v___x_3434_, 2, v___x_3432_);
lean_ctor_set(v___x_3434_, 3, v___x_3433_);
v___x_3435_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3425_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3438_ = l_Lean_Syntax_node1(v___x_3425_, v___x_3437_, v_stx_1893_);
v___x_3439_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3425_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = l_Lean_Syntax_node4(v___x_3425_, v___x_1905_, v___x_3434_, v___x_3436_, v___x_3438_, v___x_3440_);
v___x_3442_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3451_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3441_);
lean_ctor_set(v___x_3447_, 1, v_a_3443_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v___x_3441_);
v_a_3452_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3442_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3442_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v___x_3425_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3472_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3426_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3426_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3480_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3423_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3423_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_val_3488_; lean_object* v___x_3489_; 
lean_dec(v_id_1892_);
v_val_3488_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3489_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3488_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v_pat_1898_ = v_a_3490_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_stx_1893_);
v_a_3491_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3489_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3489_);
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
}
else
{
lean_object* v_stx_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec(v_id_x3f_1891_);
v_stx_3499_ = l_Lean_Syntax_getArg(v___x_3421_, v___x_2867_);
lean_dec(v___x_3421_);
v___x_3500_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3501_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2871_, v_stx_3499_, v_id_1892_, v___x_3500_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v_pat_1898_ = v_a_3502_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v_stx_1893_);
v_a_3503_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3501_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
lean_dec(v___x_2868_);
v___x_3511_ = lean_unsigned_to_nat(1u);
v___x_3512_ = lean_unsigned_to_nat(2u);
v___x_3513_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_3512_);
lean_inc(v___x_3513_);
v___x_3514_ = l_Lean_Syntax_matchesNull(v___x_3513_, v___x_3511_);
if (v___x_3514_ == 0)
{
lean_dec(v___x_3513_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = l_Lean_SourceInfo_fromRef(v_a_3516_, v___x_3514_);
lean_dec(v_a_3516_);
v___x_3518_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v_a_3521_; lean_object* v_quotContext_x3f_3552_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v_quotContext_x3f_3552_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3552_) == 0)
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v_a_3521_ = v_a_3554_;
goto v___jp_3520_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v_a_3519_);
lean_dec(v___x_3517_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3555_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3553_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_object* v_val_3563_; 
v_val_3563_ = lean_ctor_get(v_quotContext_x3f_3552_, 0);
lean_inc(v_val_3563_);
v_a_3521_ = v_val_3563_;
goto v___jp_3520_;
}
v___jp_3520_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3522_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3524_ = l_Lean_addMacroScope(v_a_3521_, v___x_3523_, v_a_3519_);
v___x_3525_ = lean_box(0);
lean_inc_n(v___x_3517_, 4);
v___x_3526_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3517_);
lean_ctor_set(v___x_3526_, 1, v___x_3522_);
lean_ctor_set(v___x_3526_, 2, v___x_3524_);
lean_ctor_set(v___x_3526_, 3, v___x_3525_);
v___x_3527_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3517_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3530_ = l_Lean_Syntax_node1(v___x_3517_, v___x_3529_, v_stx_1893_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3517_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_Syntax_node4(v___x_3517_, v___x_1905_, v___x_3526_, v___x_3528_, v___x_3530_, v___x_3532_);
v___x_3534_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3543_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3533_);
lean_ctor_set(v___x_3539_, 1, v_a_3535_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3539_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v___x_3533_);
v_a_3544_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3534_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3534_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v___x_3517_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3564_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3518_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3518_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3572_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3515_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3515_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v_val_3580_; lean_object* v___x_3581_; 
lean_dec(v_id_1892_);
v_val_3580_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3580_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3581_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3580_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v_pat_1898_ = v_a_3582_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v_stx_1893_);
v_a_3583_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3581_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3581_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
else
{
lean_object* v_stx_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec(v_id_x3f_1891_);
v_stx_3591_ = l_Lean_Syntax_getArg(v___x_3513_, v___x_2867_);
lean_dec(v___x_3513_);
v___x_3592_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3593_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2871_, v_stx_3591_, v_id_1892_, v___x_3592_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
v_pat_1898_ = v_a_3594_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_stx_1893_);
v_a_3595_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3593_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3593_);
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
}
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
lean_dec(v___x_2868_);
v___x_3603_ = lean_unsigned_to_nat(1u);
v___x_3604_ = lean_unsigned_to_nat(2u);
v___x_3605_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_3604_);
lean_inc(v___x_3605_);
v___x_3606_ = l_Lean_Syntax_matchesNull(v___x_3605_, v___x_3603_);
if (v___x_3606_ == 0)
{
lean_dec(v___x_3605_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = l_Lean_SourceInfo_fromRef(v_a_3608_, v___x_3606_);
lean_dec(v_a_3608_);
v___x_3610_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v_a_3613_; lean_object* v_quotContext_x3f_3644_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v_quotContext_x3f_3644_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3644_) == 0)
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v_a_3613_ = v_a_3646_;
goto v___jp_3612_;
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec(v_a_3611_);
lean_dec(v___x_3609_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3647_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3645_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3645_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
else
{
lean_object* v_val_3655_; 
v_val_3655_ = lean_ctor_get(v_quotContext_x3f_3644_, 0);
lean_inc(v_val_3655_);
v_a_3613_ = v_val_3655_;
goto v___jp_3612_;
}
v___jp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3614_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3616_ = l_Lean_addMacroScope(v_a_3613_, v___x_3615_, v_a_3611_);
v___x_3617_ = lean_box(0);
lean_inc_n(v___x_3609_, 4);
v___x_3618_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3609_);
lean_ctor_set(v___x_3618_, 1, v___x_3614_);
lean_ctor_set(v___x_3618_, 2, v___x_3616_);
lean_ctor_set(v___x_3618_, 3, v___x_3617_);
v___x_3619_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3609_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3622_ = l_Lean_Syntax_node1(v___x_3609_, v___x_3621_, v_stx_1893_);
v___x_3623_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3609_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_Syntax_node4(v___x_3609_, v___x_1905_, v___x_3618_, v___x_3620_, v___x_3622_, v___x_3624_);
v___x_3626_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3635_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3635_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3635_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3625_);
lean_ctor_set(v___x_3631_, 1, v_a_3627_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3631_);
v___x_3633_ = v___x_3629_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v___x_3625_);
v_a_3636_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3626_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3626_);
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
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v___x_3609_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3656_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3610_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3610_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3664_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3607_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3607_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_val_3672_; lean_object* v___x_3673_; 
lean_dec(v_id_1892_);
v_val_3672_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3673_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3672_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v_pat_1898_ = v_a_3674_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_stx_1893_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3673_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
else
{
lean_object* v_stx_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_dec(v_id_x3f_1891_);
v_stx_3683_ = l_Lean_Syntax_getArg(v___x_3605_, v___x_2867_);
lean_dec(v___x_3605_);
v___x_3684_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3685_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2869_, v_stx_3683_, v_id_1892_, v___x_3684_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v_pat_1898_ = v_a_3686_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_stx_1893_);
v_a_3687_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3685_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3685_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
}
v___jp_1906_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1912_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1913_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1914_ = l_Lean_addMacroScope(v_a_1911_, v___x_1913_, v___y_1907_);
v___x_1915_ = lean_box(0);
lean_inc_n(v___y_1908_, 4);
v___x_1916_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1916_, 0, v___y_1908_);
lean_ctor_set(v___x_1916_, 1, v___x_1912_);
lean_ctor_set(v___x_1916_, 2, v___x_1914_);
lean_ctor_set(v___x_1916_, 3, v___x_1915_);
v___x_1917_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___y_1908_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_1920_ = l_Lean_Syntax_node1(v___y_1908_, v___x_1919_, v_stx_1893_);
v___x_1921_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1908_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_Syntax_node4(v___y_1908_, v___x_1905_, v___x_1916_, v___x_1918_, v___x_1920_, v___x_1922_);
v___x_1924_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v___y_1910_, v___y_1909_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1933_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1923_);
lean_ctor_set(v___x_1929_, 1, v_a_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v___x_1923_);
v_a_1934_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1924_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1924_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
v___jp_1942_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1946_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1947_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1948_ = l_Lean_addMacroScope(v_a_1945_, v___x_1947_, v___y_1943_);
v___x_1949_ = lean_box(0);
lean_inc_n(v___y_1944_, 4);
v___x_1950_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1950_, 0, v___y_1944_);
lean_ctor_set(v___x_1950_, 1, v___x_1946_);
lean_ctor_set(v___x_1950_, 2, v___x_1948_);
lean_ctor_set(v___x_1950_, 3, v___x_1949_);
v___x_1951_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___y_1944_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_1954_ = l_Lean_Syntax_node1(v___y_1944_, v___x_1953_, v_stx_1893_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___y_1944_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_Syntax_node4(v___y_1944_, v___x_1905_, v___x_1950_, v___x_1952_, v___x_1954_, v___x_1956_);
v___x_1958_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1967_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1957_);
lean_ctor_set(v___x_1963_, 1, v_a_1959_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1963_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v___x_1957_);
v_a_1968_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1958_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1958_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
v___jp_1976_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1980_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1981_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1982_ = l_Lean_addMacroScope(v_a_1979_, v___x_1981_, v___y_1978_);
v___x_1983_ = lean_box(0);
lean_inc_n(v___y_1977_, 4);
v___x_1984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1984_, 0, v___y_1977_);
lean_ctor_set(v___x_1984_, 1, v___x_1980_);
lean_ctor_set(v___x_1984_, 2, v___x_1982_);
lean_ctor_set(v___x_1984_, 3, v___x_1983_);
v___x_1985_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1977_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_1988_ = l_Lean_Syntax_node1(v___y_1977_, v___x_1987_, v_stx_1893_);
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1977_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_Syntax_node4(v___y_1977_, v___x_1905_, v___x_1984_, v___x_1986_, v___x_1988_, v___x_1990_);
v___x_1992_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2001_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1991_);
lean_ctor_set(v___x_1997_, 1, v_a_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1997_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v___x_1991_);
v_a_2002_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1992_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1992_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
v___jp_2010_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2016_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2017_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2018_ = l_Lean_addMacroScope(v_a_2015_, v___x_2017_, v___y_2012_);
v___x_2019_ = lean_box(0);
lean_inc_n(v___y_2014_, 4);
v___x_2020_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2014_);
lean_ctor_set(v___x_2020_, 1, v___x_2016_);
lean_ctor_set(v___x_2020_, 2, v___x_2018_);
lean_ctor_set(v___x_2020_, 3, v___x_2019_);
v___x_2021_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_2014_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2024_ = l_Lean_Syntax_node1(v___y_2014_, v___x_2023_, v_stx_1893_);
v___x_2025_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___y_2014_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = l_Lean_Syntax_node4(v___y_2014_, v___x_1905_, v___x_2020_, v___x_2022_, v___x_2024_, v___x_2026_);
v___x_2028_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v___y_2011_, v___y_2013_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2037_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2027_);
lean_ctor_set(v___x_2033_, 1, v_a_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2033_);
v___x_2035_ = v___x_2031_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v___x_2027_);
v_a_2038_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2028_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2028_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
v___jp_2046_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2050_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2051_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2052_ = l_Lean_addMacroScope(v_a_2049_, v___x_2051_, v___y_2047_);
v___x_2053_ = lean_box(0);
lean_inc_n(v___y_2048_, 4);
v___x_2054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2054_, 0, v___y_2048_);
lean_ctor_set(v___x_2054_, 1, v___x_2050_);
lean_ctor_set(v___x_2054_, 2, v___x_2052_);
lean_ctor_set(v___x_2054_, 3, v___x_2053_);
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___y_2048_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2058_ = l_Lean_Syntax_node1(v___y_2048_, v___x_2057_, v_stx_1893_);
v___x_2059_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2048_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = l_Lean_Syntax_node4(v___y_2048_, v___x_1905_, v___x_2054_, v___x_2056_, v___x_2058_, v___x_2060_);
v___x_2062_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2061_);
lean_ctor_set(v___x_2067_, 1, v_a_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v___x_2061_);
v_a_2072_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2062_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2062_);
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
v___jp_2080_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2084_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2085_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2086_ = l_Lean_addMacroScope(v_a_2083_, v___x_2085_, v___y_2081_);
v___x_2087_ = lean_box(0);
lean_inc_n(v___y_2082_, 4);
v___x_2088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2088_, 0, v___y_2082_);
lean_ctor_set(v___x_2088_, 1, v___x_2084_);
lean_ctor_set(v___x_2088_, 2, v___x_2086_);
lean_ctor_set(v___x_2088_, 3, v___x_2087_);
v___x_2089_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___y_2082_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_2092_ = l_Lean_Syntax_node1(v___y_2082_, v___x_2091_, v_stx_1893_);
v___x_2093_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___y_2082_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_node4(v___y_2082_, v___x_1905_, v___x_2088_, v___x_2090_, v___x_2092_, v___x_2094_);
v___x_2096_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2095_);
lean_ctor_set(v___x_2101_, 1, v_a_2097_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v___x_2095_);
v_a_2106_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2096_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2096_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = lean_unsigned_to_nat(1u);
v___x_3696_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_3695_);
if (v___x_1902_ == 0)
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3696_);
v___x_3721_ = l_Lean_Syntax_isOfKind(v___x_3696_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_dec(v___x_3696_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3724_ = l_Lean_SourceInfo_fromRef(v_a_3723_, v___x_1902_);
lean_dec(v_a_3723_);
v___x_3725_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v_a_3728_; lean_object* v_quotContext_x3f_3760_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v_quotContext_x3f_3760_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3760_) == 0)
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v_a_3728_ = v_a_3762_;
goto v___jp_3727_;
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_a_3726_);
lean_dec(v___x_3724_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3763_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3761_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3761_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
else
{
lean_object* v_val_3771_; 
v_val_3771_ = lean_ctor_get(v_quotContext_x3f_3760_, 0);
lean_inc(v_val_3771_);
v_a_3728_ = v_val_3771_;
goto v___jp_3727_;
}
v___jp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3730_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3731_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3732_ = l_Lean_addMacroScope(v_a_3728_, v___x_3731_, v_a_3726_);
v___x_3733_ = lean_box(0);
lean_inc_n(v___x_3724_, 4);
v___x_3734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3724_);
lean_ctor_set(v___x_3734_, 1, v___x_3730_);
lean_ctor_set(v___x_3734_, 2, v___x_3732_);
lean_ctor_set(v___x_3734_, 3, v___x_3733_);
v___x_3735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3724_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3738_ = l_Lean_Syntax_node1(v___x_3724_, v___x_3737_, v_stx_1893_);
v___x_3739_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3724_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l_Lean_Syntax_node4(v___x_3724_, v___x_3729_, v___x_3734_, v___x_3736_, v___x_3738_, v___x_3740_);
v___x_3742_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3751_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3741_);
lean_ctor_set(v___x_3747_, 1, v_a_3743_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3747_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v___x_3741_);
v_a_3752_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3742_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3742_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v___x_3724_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3772_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3725_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3725_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3780_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3722_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3722_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v_val_3788_; lean_object* v___x_3789_; 
lean_dec(v_id_1892_);
v_val_3788_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3788_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3789_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3788_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v_pat_1898_ = v_a_3790_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec(v_stx_1893_);
v_a_3791_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3789_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3789_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1891_);
goto v___jp_3697_;
}
}
else
{
lean_dec(v_id_x3f_1891_);
goto v___jp_3697_;
}
v___jp_3697_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3698_, 0, v___x_3696_);
v___x_3699_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3698_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref_known(v___x_3699_, 1);
v___x_3701_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3702_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3703_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3704_ = lean_unsigned_to_nat(4u);
v___x_3705_ = lean_mk_empty_array_with_capacity(v___x_3704_);
v___x_3706_ = lean_array_push(v___x_3705_, v_a_3700_);
v___x_3707_ = lean_array_push(v___x_3706_, v___x_3702_);
v___x_3708_ = lean_array_push(v___x_3707_, v___x_3703_);
v___x_3709_ = lean_array_push(v___x_3708_, v_id_1892_);
v___x_3710_ = lean_box(2);
v___x_3711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
lean_ctor_set(v___x_3711_, 1, v___x_3701_);
lean_ctor_set(v___x_3711_, 2, v___x_3709_);
v_pat_1898_ = v___x_3711_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3712_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3699_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3699_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
v___x_3800_ = l_Lean_Syntax_getArg(v_stx_1893_, v___x_3799_);
v___x_3801_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3800_);
v___x_3802_ = l_Lean_Syntax_isOfKind(v___x_3800_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_dec(v___x_3800_);
if (lean_obj_tag(v_id_x3f_1891_) == 0)
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_Elab_Command_getRef___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___x_3805_ = l_Lean_SourceInfo_fromRef(v_a_3804_, v___x_3802_);
lean_dec(v_a_3804_);
v___x_3806_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1894_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v_a_3809_; lean_object* v_quotContext_x3f_3841_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v_quotContext_x3f_3841_ = lean_ctor_get(v_a_1894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3841_) == 0)
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1895_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v_a_3809_ = v_a_3843_;
goto v___jp_3808_;
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v_a_3807_);
lean_dec(v___x_3805_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3844_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3842_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3842_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v_val_3852_; 
v_val_3852_ = lean_ctor_get(v_quotContext_x3f_3841_, 0);
lean_inc(v_val_3852_);
v_a_3809_ = v_val_3852_;
goto v___jp_3808_;
}
v___jp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3811_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3812_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3813_ = l_Lean_addMacroScope(v_a_3809_, v___x_3812_, v_a_3807_);
v___x_3814_ = lean_box(0);
lean_inc_n(v___x_3805_, 4);
v___x_3815_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3805_);
lean_ctor_set(v___x_3815_, 1, v___x_3811_);
lean_ctor_set(v___x_3815_, 2, v___x_3813_);
lean_ctor_set(v___x_3815_, 3, v___x_3814_);
v___x_3816_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3805_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1893_);
v___x_3819_ = l_Lean_Syntax_node1(v___x_3805_, v___x_3818_, v_stx_1893_);
v___x_3820_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3805_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = l_Lean_Syntax_node4(v___x_3805_, v___x_3810_, v___x_3815_, v___x_3817_, v___x_3819_, v___x_3821_);
v___x_3823_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_id_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3832_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3832_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3832_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3822_);
lean_ctor_set(v___x_3828_, 1, v_a_3824_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3828_);
v___x_3830_ = v___x_3826_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec(v___x_3822_);
v_a_3833_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3823_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3823_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v___x_3805_);
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3853_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3806_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3806_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3861_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3803_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3803_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_val_3869_; lean_object* v___x_3870_; 
lean_dec(v_id_1892_);
v_val_3869_ = lean_ctor_get(v_id_x3f_1891_, 0);
lean_inc(v_val_3869_);
lean_dec_ref_known(v_id_x3f_1891_, 1);
lean_inc(v_stx_1893_);
v___x_3870_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1893_, v_val_3869_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v_pat_1898_ = v_a_3871_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v_stx_1893_);
v_a_3872_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3870_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3870_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_dec(v_id_x3f_1891_);
v___x_3880_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3880_, 0, v___x_3800_);
v___x_3881_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3880_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3884_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3885_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3886_ = lean_unsigned_to_nat(4u);
v___x_3887_ = lean_mk_empty_array_with_capacity(v___x_3886_);
v___x_3888_ = lean_array_push(v___x_3887_, v_a_3882_);
v___x_3889_ = lean_array_push(v___x_3888_, v___x_3884_);
v___x_3890_ = lean_array_push(v___x_3889_, v___x_3885_);
v___x_3891_ = lean_array_push(v___x_3890_, v_id_1892_);
v___x_3892_ = lean_box(2);
v___x_3893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3883_);
lean_ctor_set(v___x_3893_, 2, v___x_3891_);
v_pat_1898_ = v___x_3893_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec(v_stx_1893_);
lean_dec(v_id_1892_);
v_a_3894_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3881_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3881_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
v___jp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_stx_1893_);
lean_ctor_set(v___x_1899_, 1, v_pat_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_x3f_1891_ = stack[0].m_obj;
lean_object* v_id_1892_ = stack[1].m_obj;
lean_object* v_stx_1893_ = stack[2].m_obj;
lean_object* v_a_1894_ = stack[3].m_obj;
lean_object* v_a_1895_ = stack[4].m_obj;
lean_object* v_res_3902_;
v_res_3902_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1891_, v_id_1892_, v_stx_1893_, v_a_1894_, v_a_1895_);
stack->m_obj
 = v_res_3902_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3903_, lean_object* v_id_3904_, lean_object* v_stx_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3903_, v_id_3904_, v_stx_3905_, v_a_3906_, v_a_3907_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3910_, lean_object* v_x_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3911_, v___y_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3915_, lean_object* v_x_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3915_, v_x_3916_, v___y_3917_, v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec_ref(v_x_3916_);
return v_res_3919_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3920_, lean_object* v_ref_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3921_);
return v___x_3925_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3921_ = stack[1].m_obj;
lean_object* v___y_3922_ = stack[2].m_obj;
lean_object* v___y_3923_ = stack[3].m_obj;
lean_object* v_res_3926_;
v_res_3926_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_box(0), v_ref_3921_, v___y_3922_, v___y_3923_);
stack->m_obj
 = v_res_3926_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3927_, lean_object* v_ref_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3927_, v_ref_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
return v_res_3932_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3937_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3934_ = stack[1].m_obj;
lean_object* v___y_3935_ = stack[2].m_obj;
lean_object* v_res_3938_;
v_res_3938_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_box(0), v___y_3934_, v___y_3935_);
stack->m_obj
 = v_res_3938_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
return v_res_3943_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3944_, lean_object* v_x_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3945_, v___y_3946_, v___y_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3945_ = stack[1].m_obj;
lean_object* v___y_3946_ = stack[2].m_obj;
lean_object* v___y_3947_ = stack[3].m_obj;
lean_object* v_res_3950_;
v_res_3950_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_box(0), v_x_3945_, v___y_3946_, v___y_3947_);
stack->m_obj
 = v_res_3950_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3951_, lean_object* v_x_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3951_, v_x_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
return v_res_3956_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3957_, lean_object* v_as_x27_3958_, lean_object* v_b_3959_, lean_object* v_a_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3958_, v_b_3959_, v___y_3961_, v___y_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3957_ = stack[0].m_obj;
lean_object* v_as_x27_3958_ = stack[1].m_obj;
lean_object* v_b_3959_ = stack[2].m_obj;
lean_object* v___y_3961_ = stack[4].m_obj;
lean_object* v___y_3962_ = stack[5].m_obj;
lean_object* v_res_3965_;
v_res_3965_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3957_, v_as_x27_3958_, v_b_3959_, lean_box(0), v___y_3961_, v___y_3962_);
stack->m_obj
 = v_res_3965_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3966_, lean_object* v_as_x27_3967_, lean_object* v_b_3968_, lean_object* v_a_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3966_, v_as_x27_3967_, v_b_3968_, v_a_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v_as_x27_3967_);
lean_dec(v_as_3966_);
return v_res_3973_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3974_, lean_object* v_ref_3975_, lean_object* v_msg_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3975_, v_msg_3976_, v___y_3977_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3975_ = stack[1].m_obj;
lean_object* v_msg_3976_ = stack[2].m_obj;
lean_object* v___y_3977_ = stack[3].m_obj;
lean_object* v___y_3978_ = stack[4].m_obj;
lean_object* v_res_3981_;
v_res_3981_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_box(0), v_ref_3975_, v_msg_3976_, v___y_3977_, v___y_3978_);
stack->m_obj
 = v_res_3981_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3982_, lean_object* v_ref_3983_, lean_object* v_msg_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3982_, v_ref_3983_, v_msg_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v_ref_3983_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3989_, lean_object* v_m_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3990_, v_a_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3993_, lean_object* v_m_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3993_, v_m_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_m_3994_);
return v_res_3996_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3997_, lean_object* v_x_3998_, lean_object* v_x_3999_){
_start:
{
uint8_t v___x_4000_; 
v___x_4000_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3998_, v_x_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3998_ = stack[1].m_obj;
lean_object* v_x_3999_ = stack[2].m_obj;
uint8_t v_res_4001_;
v_res_4001_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_box(0), v_x_3998_, v_x_3999_);
stack->m_num = v_res_4001_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_4002_, lean_object* v_x_4003_, lean_object* v_x_4004_){
_start:
{
uint8_t v_res_4005_; lean_object* v_r_4006_; 
v_res_4005_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_4002_, v_x_4003_, v_x_4004_);
lean_dec_ref(v_x_4004_);
lean_dec_ref(v_x_4003_);
v_r_4006_ = lean_box(v_res_4005_);
return v_r_4006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_4007_, lean_object* v_a_4008_, lean_object* v_x_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_4008_, v_x_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_4011_, lean_object* v_a_4012_, lean_object* v_x_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_4011_, v_a_4012_, v_x_4013_);
lean_dec(v_x_4013_);
lean_dec(v_a_4012_);
return v_res_4014_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_4015_, lean_object* v_x_4016_, size_t v_x_4017_, lean_object* v_x_4018_){
_start:
{
uint8_t v___x_4019_; 
v___x_4019_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_4016_, v_x_4017_, v_x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4016_ = stack[1].m_obj;
size_t v_x_4017_ = stack[2].m_num;
lean_object* v_x_4018_ = stack[3].m_obj;
uint8_t v_res_4020_;
v_res_4020_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_box(0), v_x_4016_, v_x_4017_, v_x_4018_);
stack->m_num = v_res_4020_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_){
_start:
{
size_t v_x_51031__boxed_4025_; uint8_t v_res_4026_; lean_object* v_r_4027_; 
v_x_51031__boxed_4025_ = lean_unbox_usize(v_x_4023_);
lean_dec(v_x_4023_);
v_res_4026_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_4021_, v_x_4022_, v_x_51031__boxed_4025_, v_x_4024_);
lean_dec_ref(v_x_4024_);
lean_dec_ref(v_x_4022_);
v_r_4027_ = lean_box(v_res_4026_);
return v_r_4027_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_4028_, lean_object* v_keys_4029_, lean_object* v_vals_4030_, lean_object* v_heq_4031_, lean_object* v_i_4032_, lean_object* v_k_4033_){
_start:
{
uint8_t v___x_4034_; 
v___x_4034_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_4029_, v_i_4032_, v_k_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_4029_ = stack[1].m_obj;
lean_object* v_vals_4030_ = stack[2].m_obj;
lean_object* v_i_4032_ = stack[4].m_obj;
lean_object* v_k_4033_ = stack[5].m_obj;
uint8_t v_res_4035_;
v_res_4035_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_box(0), v_keys_4029_, v_vals_4030_, lean_box(0), v_i_4032_, v_k_4033_);
stack->m_num = v_res_4035_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_4036_, lean_object* v_keys_4037_, lean_object* v_vals_4038_, lean_object* v_heq_4039_, lean_object* v_i_4040_, lean_object* v_k_4041_){
_start:
{
uint8_t v_res_4042_; lean_object* v_r_4043_; 
v_res_4042_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_4036_, v_keys_4037_, v_vals_4038_, v_heq_4039_, v_i_4040_, v_k_4041_);
lean_dec_ref(v_k_4041_);
lean_dec_ref(v_vals_4038_);
lean_dec_ref(v_keys_4037_);
v_r_4043_ = lean_box(v_res_4042_);
return v_r_4043_;
}
}
uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_k_4050_){
_start:
{
lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4051_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_4052_ = lean_name_eq(v_k_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
uint8_t v___x_4053_; 
v___x_4053_ = 1;
return v___x_4053_;
}
else
{
uint8_t v___x_4054_; 
v___x_4054_ = 0;
return v___x_4054_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_expandMacroArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4050_ = stack[0].m_obj;
uint8_t v_res_4055_;
v_res_4055_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_4050_);
stack->m_num = v_res_4055_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_k_4056_){
_start:
{
uint8_t v_res_4057_; lean_object* v_r_4058_; 
v_res_4057_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_k_4056_);
lean_dec(v_k_4056_);
v_r_4058_ = lean_box(v_res_4057_);
return v_r_4058_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_4069_ = l_String_toRawSubstring_x27(v___x_4068_);
return v___x_4069_;
}
}
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___f_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___f_4076_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_4077_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_4077_, 0, v_stx_4072_);
lean_closure_set(v___x_4077_, 1, v___f_4076_);
v___x_4078_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_4077_, v_a_4073_, v_a_4074_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc_n(v_a_4079_, 2);
lean_dec_ref_known(v___x_4078_, 1);
v___x_4080_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_4081_ = l_Lean_Syntax_isOfKind(v_a_4079_, v___x_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_a_4079_);
v___x_4082_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4091_ = lean_unsigned_to_nat(0u);
v___x_4092_ = l_Lean_Syntax_getArg(v_a_4079_, v___x_4091_);
v___x_4093_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4092_);
v___x_4094_ = l_Lean_Syntax_matchesNull(v___x_4092_, v___x_4093_);
if (v___x_4094_ == 0)
{
uint8_t v___x_4095_; 
v___x_4095_ = l_Lean_Syntax_matchesNull(v___x_4092_, v___x_4091_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_a_4079_);
v___x_4096_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
else
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4105_ = lean_unsigned_to_nat(1u);
v___x_4106_ = l_Lean_Syntax_getArg(v_a_4079_, v___x_4105_);
lean_dec(v_a_4079_);
v___x_4107_ = l_Lean_Elab_Command_getRef___redArg(v_a_4073_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4107_, 1);
v___x_4109_ = l_Lean_SourceInfo_fromRef(v_a_4108_, v___x_4094_);
lean_dec(v_a_4108_);
v___x_4110_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4073_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v_a_4113_; lean_object* v_quotContext_x3f_4121_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___x_4110_, 1);
v_quotContext_x3f_4121_ = lean_ctor_get(v_a_4073_, 5);
if (lean_obj_tag(v_quotContext_x3f_4121_) == 0)
{
lean_object* v___x_4122_; lean_object* v_a_4123_; 
v___x_4122_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_4074_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref(v___x_4122_);
v_a_4113_ = v_a_4123_;
goto v___jp_4112_;
}
else
{
lean_object* v_val_4124_; 
v_val_4124_ = lean_ctor_get(v_quotContext_x3f_4121_, 0);
lean_inc(v_val_4124_);
v_a_4113_ = v_val_4124_;
goto v___jp_4112_;
}
v___jp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4114_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_4115_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_4116_ = l_Lean_addMacroScope(v_a_4113_, v___x_4115_, v_a_4111_);
v___x_4117_ = lean_box(0);
v___x_4118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4109_);
lean_ctor_set(v___x_4118_, 1, v___x_4114_);
lean_ctor_set(v___x_4118_, 2, v___x_4116_);
lean_ctor_set(v___x_4118_, 3, v___x_4117_);
v___x_4119_ = lean_box(0);
v___x_4120_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4119_, v___x_4118_, v___x_4106_, v_a_4073_, v_a_4074_);
return v___x_4120_;
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v___x_4109_);
lean_dec(v___x_4106_);
v_a_4125_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4110_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4110_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec(v___x_4106_);
v_a_4133_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4107_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4107_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v___x_4141_ = l_Lean_Syntax_getArg(v___x_4092_, v___x_4091_);
lean_dec(v___x_4092_);
v___x_4142_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_4141_);
v___x_4143_ = l_Lean_Syntax_isOfKind(v___x_4141_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v___x_4141_);
lean_dec(v_a_4079_);
v___x_4144_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = lean_unsigned_to_nat(1u);
v___x_4154_ = l_Lean_Syntax_getArg(v_a_4079_, v___x_4153_);
lean_dec(v_a_4079_);
lean_inc(v___x_4141_);
v___x_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4141_);
v___x_4156_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_4155_, v___x_4141_, v___x_4154_, v_a_4073_, v_a_4074_);
return v___x_4156_;
}
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
v_a_4157_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4078_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4078_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_expandMacroArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4072_ = stack[0].m_obj;
lean_object* v_a_4073_ = stack[1].m_obj;
lean_object* v_a_4074_ = stack[2].m_obj;
lean_object* v_res_4165_;
v_res_4165_ = l_Lean_Elab_Command_expandMacroArg(v_stx_4072_, v_a_4073_, v_a_4074_);
stack->m_obj
 = v_res_4165_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Elab_Command_expandMacroArg(v_stx_4166_, v_a_4167_, v_a_4168_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4170_;
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
