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
lean_object* l_Lean_Elab_Term_expandMacrosReportingDeprecated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_14935__boxed_65_; uint8_t v___x_14936__boxed_66_; lean_object* v_res_67_; 
v___x_14935__boxed_65_ = lean_unbox(v___x_59_);
v___x_14936__boxed_66_ = lean_unbox(v___x_60_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_57_, v___x_58_, v___x_14935__boxed_65_, v___x_14936__boxed_66_, v_x_61_, v___y_62_, v___y_63_);
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
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___y_111_; uint8_t v___x_122_; 
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_array_uget_borrowed(v_as_91_, v_i_92_);
lean_inc(v___x_107_);
v___x_122_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_104_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_107_);
v___x_124_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_123_);
if (v___x_124_ == 0)
{
goto v___jp_108_;
}
else
{
lean_object* v_id_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_id_125_ = l_Lean_Syntax_getArg(v___x_107_, v___x_105_);
v___x_126_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_125_);
v___x_127_ = l_Lean_Syntax_isOfKind(v_id_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v_id_125_);
goto v___jp_108_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = l_Lean_Syntax_getArg(v___x_107_, v___x_128_);
v___x_130_ = l_Lean_Syntax_matchesNull(v___x_129_, v___x_106_);
if (v___x_130_ == 0)
{
lean_dec(v_id_125_);
goto v___jp_108_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = l_Lean_TSyntax_getId(v_id_125_);
lean_dec(v_id_125_);
v___x_132_ = l_Lean_Parser_getParserAliasInfo(v___x_131_);
lean_dec(v___x_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v_stackSz_x3f_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_132_, 1);
v_stackSz_x3f_134_ = lean_ctor_get(v_a_133_, 1);
lean_inc(v_stackSz_x3f_134_);
lean_dec(v_a_133_);
v___x_135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_136_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_134_, v___x_135_);
lean_dec(v_stackSz_x3f_134_);
if (v___x_136_ == 0)
{
goto v___jp_108_;
}
else
{
v_a_99_ = v_b_94_;
goto v___jp_98_;
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_149_; 
lean_dec_ref(v_b_94_);
v_a_137_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_149_ == 0)
{
v___x_139_ = v___x_132_;
v_isShared_140_ = v_isSharedCheck_149_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_132_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_149_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v_ref_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v_ref_141_ = lean_ctor_get(v___y_95_, 7);
v___x_142_ = lean_io_error_to_string(v_a_137_);
v___x_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = l_Lean_MessageData_ofFormat(v___x_143_);
lean_inc(v_ref_141_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_ref_141_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_145_);
v___x_147_ = v___x_139_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_id_150_ = l_Lean_Syntax_getArg(v___x_107_, v___x_105_);
v___x_151_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_150_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_id_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_id_150_);
goto v___jp_108_;
}
else
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = l_Lean_Syntax_getArg(v___x_107_, v___x_106_);
v___x_154_ = l_Lean_Syntax_isNone(v___x_153_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_matchesNull(v___x_153_, v___x_106_);
if (v___x_155_ == 0)
{
lean_dec(v___x_153_);
lean_dec(v_id_150_);
goto v___jp_108_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_157_ = l_Lean_Syntax_getArg(v___x_153_, v___x_105_);
lean_dec(v___x_153_);
v___x_158_ = l_Lean_Syntax_isOfKind(v___x_157_, v___x_156_);
if (v___x_158_ == 0)
{
lean_dec(v_id_150_);
goto v___jp_108_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(0);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_150_, v___x_105_, v___x_122_, v___x_90_, v___x_159_, v___y_95_, v___y_96_);
lean_dec(v_id_150_);
v___y_111_ = v___x_160_;
goto v___jp_110_;
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_153_);
v___x_161_ = lean_box(0);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_150_, v___x_105_, v___x_122_, v___x_90_, v___x_161_, v___y_95_, v___y_96_);
lean_dec(v_id_150_);
v___y_111_ = v___x_162_;
goto v___jp_110_;
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
if (lean_obj_tag(v___y_111_) == 0)
{
lean_object* v_a_112_; uint8_t v___x_113_; 
v_a_112_ = lean_ctor_get(v___y_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___y_111_, 1);
v___x_113_ = lean_unbox(v_a_112_);
lean_dec(v_a_112_);
if (v___x_113_ == 0)
{
v_a_99_ = v_b_94_;
goto v___jp_98_;
}
else
{
goto v___jp_108_;
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
lean_dec_ref(v_b_94_);
v_a_114_ = lean_ctor_get(v___y_111_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___y_111_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___y_111_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___y_111_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v_b_94_);
return v___x_163_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___boxed(lean_object* v___x_164_, lean_object* v_as_165_, lean_object* v_i_166_, lean_object* v_stop_167_, lean_object* v_b_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v___x_15063__boxed_172_; size_t v_i_boxed_173_; size_t v_stop_boxed_174_; lean_object* v_res_175_; 
v___x_15063__boxed_172_ = lean_unbox(v___x_164_);
v_i_boxed_173_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_stop_boxed_174_ = lean_unbox_usize(v_stop_167_);
lean_dec(v_stop_167_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_15063__boxed_172_, v_as_165_, v_i_boxed_173_, v_stop_boxed_174_, v_b_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec_ref(v_as_165_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(uint8_t v___x_176_, lean_object* v_as_177_, size_t v_i_178_, size_t v_stop_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_a_185_; uint8_t v___x_189_; 
v___x_189_ = lean_usize_dec_eq(v_i_178_, v_stop_179_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___y_197_; uint8_t v___x_208_; 
v___x_190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_array_uget_borrowed(v_as_177_, v_i_178_);
lean_inc(v___x_193_);
v___x_208_ = l_Lean_Syntax_isOfKind(v___x_193_, v___x_190_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_193_);
v___x_210_ = l_Lean_Syntax_isOfKind(v___x_193_, v___x_209_);
if (v___x_210_ == 0)
{
goto v___jp_194_;
}
else
{
lean_object* v_id_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_id_211_ = l_Lean_Syntax_getArg(v___x_193_, v___x_191_);
v___x_212_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_211_);
v___x_213_ = l_Lean_Syntax_isOfKind(v_id_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec(v_id_211_);
goto v___jp_194_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(2u);
v___x_215_ = l_Lean_Syntax_getArg(v___x_193_, v___x_214_);
v___x_216_ = l_Lean_Syntax_matchesNull(v___x_215_, v___x_192_);
if (v___x_216_ == 0)
{
lean_dec(v_id_211_);
goto v___jp_194_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = l_Lean_TSyntax_getId(v_id_211_);
lean_dec(v_id_211_);
v___x_218_ = l_Lean_Parser_getParserAliasInfo(v___x_217_);
lean_dec(v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v_stackSz_x3f_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v_stackSz_x3f_220_ = lean_ctor_get(v_a_219_, 1);
lean_inc(v_stackSz_x3f_220_);
lean_dec(v_a_219_);
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_222_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_220_, v___x_221_);
lean_dec(v_stackSz_x3f_220_);
if (v___x_222_ == 0)
{
goto v___jp_194_;
}
else
{
v_a_185_ = v_b_180_;
goto v___jp_184_;
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_b_180_);
v_a_223_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_235_ == 0)
{
v___x_225_ = v___x_218_;
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_218_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_ref_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v_ref_227_ = lean_ctor_get(v___y_181_, 7);
v___x_228_ = lean_io_error_to_string(v_a_223_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = l_Lean_MessageData_ofFormat(v___x_229_);
lean_inc(v_ref_227_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_ref_227_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_231_);
v___x_233_ = v___x_225_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
}
}
else
{
lean_object* v_id_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_id_236_ = l_Lean_Syntax_getArg(v___x_193_, v___x_191_);
v___x_237_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_236_);
v___x_238_ = l_Lean_Syntax_isOfKind(v_id_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_id_236_);
goto v___jp_194_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = l_Lean_Syntax_getArg(v___x_193_, v___x_192_);
v___x_240_ = l_Lean_Syntax_isNone(v___x_239_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
lean_inc(v___x_239_);
v___x_241_ = l_Lean_Syntax_matchesNull(v___x_239_, v___x_192_);
if (v___x_241_ == 0)
{
lean_dec(v___x_239_);
lean_dec(v_id_236_);
goto v___jp_194_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = l_Lean_Syntax_getArg(v___x_239_, v___x_191_);
lean_dec(v___x_239_);
v___x_243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_244_ = l_Lean_Syntax_isOfKind(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v_id_236_);
goto v___jp_194_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(0);
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_236_, v___x_191_, v___x_208_, v___x_176_, v___x_245_, v___y_181_, v___y_182_);
lean_dec(v_id_236_);
v___y_197_ = v___x_246_;
goto v___jp_196_;
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_239_);
v___x_247_ = lean_box(0);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_236_, v___x_191_, v___x_208_, v___x_176_, v___x_247_, v___y_181_, v___y_182_);
lean_dec(v_id_236_);
v___y_197_ = v___x_248_;
goto v___jp_196_;
}
}
}
v___jp_194_:
{
lean_object* v___x_195_; 
lean_inc(v___x_193_);
v___x_195_ = lean_array_push(v_b_180_, v___x_193_);
v_a_185_ = v___x_195_;
goto v___jp_184_;
}
v___jp_196_:
{
if (lean_obj_tag(v___y_197_) == 0)
{
lean_object* v_a_198_; uint8_t v___x_199_; 
v_a_198_ = lean_ctor_get(v___y_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___y_197_, 1);
v___x_199_ = lean_unbox(v_a_198_);
lean_dec(v_a_198_);
if (v___x_199_ == 0)
{
v_a_185_ = v_b_180_;
goto v___jp_184_;
}
else
{
goto v___jp_194_;
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_b_180_);
v_a_200_ = lean_ctor_get(v___y_197_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___y_197_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___y_197_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___y_197_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
else
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_b_180_);
return v___x_249_;
}
v___jp_184_:
{
size_t v___x_186_; size_t v___x_187_; 
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_add(v_i_178_, v___x_186_);
v_i_178_ = v___x_187_;
v_b_180_ = v_a_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3___boxed(lean_object* v___x_250_, lean_object* v_as_251_, lean_object* v_i_252_, lean_object* v_stop_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
uint8_t v___x_15249__boxed_258_; size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v___x_15249__boxed_258_ = lean_unbox(v___x_250_);
v_i_boxed_259_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_253_);
lean_dec(v_stop_253_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_15249__boxed_258_, v_as_251_, v_i_boxed_259_, v_stop_boxed_260_, v_b_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_as_251_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(lean_object* v_opts_262_, lean_object* v_opt_263_){
_start:
{
lean_object* v_name_264_; lean_object* v_defValue_265_; lean_object* v_map_266_; lean_object* v___x_267_; 
v_name_264_ = lean_ctor_get(v_opt_263_, 0);
v_defValue_265_ = lean_ctor_get(v_opt_263_, 1);
v_map_266_ = lean_ctor_get(v_opts_262_, 0);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_266_, v_name_264_);
if (lean_obj_tag(v___x_267_) == 0)
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_defValue_265_);
return v___x_268_;
}
else
{
lean_object* v_val_269_; 
v_val_269_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v___x_267_, 1);
if (lean_obj_tag(v_val_269_) == 1)
{
uint8_t v_v_270_; 
v_v_270_ = lean_ctor_get_uint8(v_val_269_, 0);
lean_dec_ref_known(v_val_269_, 0);
return v_v_270_;
}
else
{
uint8_t v___x_271_; 
lean_dec(v_val_269_);
v___x_271_ = lean_unbox(v_defValue_265_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_272_, lean_object* v_opt_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_272_, v_opt_273_);
lean_dec_ref(v_opt_273_);
lean_dec_ref(v_opts_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(1);
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__2));
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
return v_x_283_;
}
else
{
lean_object* v_head_285_; lean_object* v_tail_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_308_; 
v_head_285_ = lean_ctor_get(v_x_284_, 0);
v_tail_286_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_308_ == 0)
{
v___x_288_ = v_x_284_;
v_isShared_289_ = v_isSharedCheck_308_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_tail_286_);
lean_inc(v_head_285_);
lean_dec(v_x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_308_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_before_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_306_; 
v_before_290_ = lean_ctor_get(v_head_285_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_head_285_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_head_285_, 1);
lean_dec(v_unused_307_);
v___x_292_ = v_head_285_;
v_isShared_293_ = v_isSharedCheck_306_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_before_290_);
lean_dec(v_head_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_306_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 7);
lean_ctor_set(v___x_292_, 1, v___x_294_);
lean_ctor_set(v___x_292_, 0, v_x_283_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_x_283_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_305_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 7);
lean_ctor_set(v___x_288_, 1, v___x_297_);
lean_ctor_set(v___x_288_, 0, v___x_296_);
v___x_299_ = v___x_288_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_304_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_MessageData_ofSyntax(v_before_290_);
v___x_301_ = l_Lean_indentD(v___x_300_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v_x_283_ = v___x_302_;
v_x_284_ = v_tail_286_;
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
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__1));
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(lean_object* v_msgData_314_, lean_object* v_macroStack_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_scopes_320_; lean_object* v___x_321_; lean_object* v_opts_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_318_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_319_ = lean_st_ref_get(v___y_316_);
v_scopes_320_ = lean_ctor_get(v___x_319_, 2);
lean_inc(v_scopes_320_);
lean_dec(v___x_319_);
v___x_321_ = l_List_head_x21___redArg(v___x_318_, v_scopes_320_);
lean_dec(v_scopes_320_);
v_opts_322_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_opts_322_);
lean_dec(v___x_321_);
v___x_323_ = l_Lean_Elab_pp_macroStack;
v___x_324_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__4(v_opts_322_, v___x_323_);
lean_dec_ref(v_opts_322_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_macroStack_315_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_msgData_314_);
return v___x_325_;
}
else
{
if (lean_obj_tag(v_macroStack_315_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_msgData_314_);
return v___x_326_;
}
else
{
lean_object* v_head_327_; lean_object* v_after_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_343_; 
v_head_327_ = lean_ctor_get(v_macroStack_315_, 0);
lean_inc(v_head_327_);
v_after_328_ = lean_ctor_get(v_head_327_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_head_327_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_head_327_, 0);
lean_dec(v_unused_344_);
v___x_330_ = v_head_327_;
v_isShared_331_ = v_isSharedCheck_343_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_after_328_);
lean_dec(v_head_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_343_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 7);
lean_ctor_set(v___x_330_, 1, v___x_332_);
lean_ctor_set(v___x_330_, 0, v_msgData_314_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_msgData_314_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_342_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_msgData_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_335_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___closed__2);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_MessageData_ofSyntax(v_after_328_);
v___x_338_ = l_Lean_indentD(v___x_337_);
v_msgData_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_339_, 0, v___x_336_);
lean_ctor_set(v_msgData_339_, 1, v___x_338_);
v___x_340_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3_spec__5(v_msgData_339_, v_macroStack_315_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_345_, lean_object* v_macroStack_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_345_, v_macroStack_346_, v___y_347_);
lean_dec(v___y_347_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_350_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_354_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
lean_ctor_set(v___x_356_, 3, v___x_355_);
lean_ctor_set(v___x_356_, 4, v___x_354_);
lean_ctor_set(v___x_356_, 5, v___x_354_);
lean_ctor_set(v___x_356_, 6, v___x_354_);
lean_ctor_set(v___x_356_, 7, v___x_354_);
lean_ctor_set(v___x_356_, 8, v___x_354_);
lean_ctor_set(v___x_356_, 9, v___x_354_);
lean_ctor_set(v___x_356_, 10, v___x_354_);
lean_ctor_set(v___x_356_, 11, v___x_353_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_unsigned_to_nat(32u);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_360_ = ((size_t)5ULL);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_unsigned_to_nat(32u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_365_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_361_);
lean_ctor_set(v___x_365_, 3, v___x_361_);
lean_ctor_set_usize(v___x_365_, 4, v___x_360_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_box(1);
v___x_367_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set(v___x_369_, 2, v___x_366_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v_env_374_; uint8_t v___x_375_; lean_object* v_env_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_scopes_379_; lean_object* v___x_380_; lean_object* v_opts_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_373_ = lean_st_ref_get(v___y_371_);
v_env_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc_ref(v_env_374_);
lean_dec(v___x_373_);
v___x_375_ = 0;
v_env_376_ = l_Lean_Environment_setRecordingDeps(v_env_374_, v___x_375_);
v___x_377_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_378_ = lean_st_ref_get(v___y_371_);
v_scopes_379_ = lean_ctor_get(v___x_378_, 2);
lean_inc(v_scopes_379_);
lean_dec(v___x_378_);
v___x_380_ = l_List_head_x21___redArg(v___x_377_, v_scopes_379_);
lean_dec(v_scopes_379_);
v_opts_381_ = lean_ctor_get(v___x_380_, 1);
lean_inc_ref(v_opts_381_);
lean_dec(v___x_380_);
v___x_382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_383_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_384_, 0, v_env_376_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set(v___x_384_, 3, v_opts_381_);
v___x_385_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_msgData_370_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_387_, v___y_388_);
lean_dec(v___y_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Elab_Command_getRef___redArg(v___y_392_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v_macroStack_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v_macroStack_397_ = lean_ctor_get(v___y_392_, 4);
v___x_398_ = l_Lean_Elab_getBetterRef(v_a_396_, v_macroStack_397_);
lean_dec(v_a_396_);
v___x_399_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_391_, v___y_393_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_399_);
lean_inc(v_macroStack_397_);
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_400_, v_macroStack_397_, v___y_393_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_398_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v_msg_391_);
v_a_411_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_395_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_395_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t v___x_424_, lean_object* v_as_425_, size_t v_i_426_, size_t v_stop_427_, lean_object* v_b_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_a_433_; uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_eq(v_i_426_, v_stop_427_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___y_443_; uint8_t v___x_454_; 
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_439_ = lean_array_uget_borrowed(v_as_425_, v_i_426_);
lean_inc(v___x_439_);
v___x_454_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_438_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_439_);
v___x_456_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_455_);
if (v___x_456_ == 0)
{
goto v___jp_440_;
}
else
{
lean_object* v___x_457_; lean_object* v_id_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v_id_458_ = l_Lean_Syntax_getArg(v___x_439_, v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_458_);
v___x_460_ = l_Lean_Syntax_isOfKind(v_id_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_id_458_);
goto v___jp_440_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_unsigned_to_nat(2u);
v___x_463_ = l_Lean_Syntax_getArg(v___x_439_, v___x_462_);
v___x_464_ = l_Lean_Syntax_matchesNull(v___x_463_, v___x_461_);
if (v___x_464_ == 0)
{
lean_dec(v_id_458_);
goto v___jp_440_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = l_Lean_TSyntax_getId(v_id_458_);
lean_dec(v_id_458_);
v___x_466_ = l_Lean_Parser_getParserAliasInfo(v___x_465_);
lean_dec(v___x_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v_stackSz_x3f_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v_stackSz_x3f_468_ = lean_ctor_get(v_a_467_, 1);
lean_inc(v_stackSz_x3f_468_);
lean_dec(v_a_467_);
v___x_469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_470_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_468_, v___x_469_);
lean_dec(v_stackSz_x3f_468_);
if (v___x_470_ == 0)
{
goto v___jp_440_;
}
else
{
v_a_433_ = v_b_428_;
goto v___jp_432_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v_b_428_);
v_a_471_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_473_ = v___x_466_;
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_466_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_ref_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_ref_475_ = lean_ctor_get(v___y_429_, 7);
v___x_476_ = lean_io_error_to_string(v_a_471_);
v___x_477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
v___x_478_ = l_Lean_MessageData_ofFormat(v___x_477_);
lean_inc(v_ref_475_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_ref_475_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_479_);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_484_; lean_object* v_id_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v_id_485_ = l_Lean_Syntax_getArg(v___x_439_, v___x_484_);
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_485_);
v___x_487_ = l_Lean_Syntax_isOfKind(v_id_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec(v_id_485_);
goto v___jp_440_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = l_Lean_Syntax_getArg(v___x_439_, v___x_488_);
v___x_490_ = l_Lean_Syntax_isNone(v___x_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
lean_inc(v___x_489_);
v___x_491_ = l_Lean_Syntax_matchesNull(v___x_489_, v___x_488_);
if (v___x_491_ == 0)
{
lean_dec(v___x_489_);
lean_dec(v_id_485_);
goto v___jp_440_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = l_Lean_Syntax_getArg(v___x_489_, v___x_484_);
lean_dec(v___x_489_);
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_494_ = l_Lean_Syntax_isOfKind(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_id_485_);
goto v___jp_440_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_box(0);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_485_, v___x_484_, v___x_454_, v___x_424_, v___x_495_, v___y_429_, v___y_430_);
lean_dec(v_id_485_);
v___y_443_ = v___x_496_;
goto v___jp_442_;
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v___x_489_);
v___x_497_ = lean_box(0);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_485_, v___x_484_, v___x_454_, v___x_424_, v___x_497_, v___y_429_, v___y_430_);
lean_dec(v_id_485_);
v___y_443_ = v___x_498_;
goto v___jp_442_;
}
}
}
v___jp_440_:
{
lean_object* v___x_441_; 
lean_inc(v___x_439_);
v___x_441_ = lean_array_push(v_b_428_, v___x_439_);
v_a_433_ = v___x_441_;
goto v___jp_432_;
}
v___jp_442_:
{
if (lean_obj_tag(v___y_443_) == 0)
{
lean_object* v_a_444_; uint8_t v___x_445_; 
v_a_444_ = lean_ctor_get(v___y_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___y_443_, 1);
v___x_445_ = lean_unbox(v_a_444_);
lean_dec(v_a_444_);
if (v___x_445_ == 0)
{
v_a_433_ = v_b_428_;
goto v___jp_432_;
}
else
{
goto v___jp_440_;
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_b_428_);
v_a_446_ = lean_ctor_get(v___y_443_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___y_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___y_443_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___y_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_b_428_);
return v___x_499_;
}
v___jp_432_:
{
size_t v___x_434_; size_t v___x_435_; 
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_426_, v___x_434_);
v_i_426_ = v___x_435_;
v_b_428_ = v_a_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v___x_500_, lean_object* v_as_501_, lean_object* v_i_502_, lean_object* v_stop_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_15734__boxed_508_; size_t v_i_boxed_509_; size_t v_stop_boxed_510_; lean_object* v_res_511_; 
v___x_15734__boxed_508_ = lean_unbox(v___x_500_);
v_i_boxed_509_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_503_);
lean_dec(v_stop_503_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_15734__boxed_508_, v_as_501_, v_i_boxed_509_, v_stop_boxed_510_, v_b_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_as_501_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(0);
v___x_525_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_533_);
v___x_541_ = l_Lean_Syntax_isOfKind(v_a_533_, v___x_540_);
v___x_542_ = 1;
if (v___x_541_ == 0)
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_533_);
v___x_550_ = l_Lean_Syntax_isOfKind(v_a_533_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v_a_533_);
goto v___jp_543_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_a_556_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = l_Lean_Syntax_getArg(v_a_533_, v___x_551_);
lean_dec(v_a_533_);
v___x_553_ = l_Lean_Syntax_getArgs(v___x_552_);
lean_dec(v___x_552_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_size(v___x_553_);
v___x_562_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_563_ = lean_nat_dec_lt(v___x_554_, v___x_561_);
if (v___x_563_ == 0)
{
lean_dec_ref(v___x_553_);
v_a_556_ = v___x_562_;
goto v___jp_555_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_561_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_541_, v___x_553_, v___x_564_, v___x_565_, v___x_562_, v_a_535_, v_a_536_);
lean_dec_ref(v___x_553_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v_a_556_ = v_a_567_;
goto v___jp_555_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_a_534_);
v_a_568_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_566_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
v___jp_555_:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_a_556_);
v___x_558_ = lean_nat_dec_eq(v___x_557_, v___x_551_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_a_556_);
goto v___jp_543_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_array_fget(v_a_556_, v___x_554_);
lean_dec_ref(v_a_556_);
v_a_533_ = v___x_559_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___y_588_; lean_object* v___y_594_; lean_object* v_id_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v_id_604_ = l_Lean_Syntax_getArg(v_a_533_, v___x_576_);
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_604_);
v___x_607_ = l_Lean_Syntax_isOfKind(v_id_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
lean_dec(v_id_604_);
v___x_608_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_533_);
v___x_609_ = l_Lean_Syntax_isOfKind(v_a_533_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_a_533_);
goto v___jp_599_;
}
else
{
lean_object* v___x_610_; lean_object* v_a_612_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_617_ = l_Lean_Syntax_getArg(v_a_533_, v___x_610_);
lean_dec(v_a_533_);
v___x_618_ = l_Lean_Syntax_getArgs(v___x_617_);
lean_dec(v___x_617_);
v___x_619_ = lean_array_get_size(v___x_618_);
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_621_ = lean_nat_dec_lt(v___x_576_, v___x_619_);
if (v___x_621_ == 0)
{
lean_dec_ref(v___x_618_);
v_a_612_ = v___x_620_;
goto v___jp_611_;
}
else
{
size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v___x_622_ = ((size_t)0ULL);
v___x_623_ = lean_usize_of_nat(v___x_619_);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_607_, v___x_618_, v___x_622_, v___x_623_, v___x_620_, v_a_535_, v_a_536_);
lean_dec_ref(v___x_618_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_a_612_ = v_a_625_;
goto v___jp_611_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_a_534_);
v_a_626_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_624_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
v___jp_611_:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_get_size(v_a_612_);
v___x_614_ = lean_nat_dec_eq(v___x_613_, v___x_610_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_a_612_);
goto v___jp_599_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_fget(v_a_612_, v___x_576_);
lean_dec_ref(v_a_612_);
v_a_533_ = v___x_615_;
goto _start;
}
}
}
}
else
{
lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___x_716_; lean_object* v_a_718_; lean_object* v_a_724_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_729_ = l_Lean_Syntax_getArg(v_a_533_, v___x_716_);
v___x_730_ = l_Lean_Syntax_isNone(v___x_729_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
lean_inc(v___x_729_);
v___x_731_ = l_Lean_Syntax_matchesNull(v___x_729_, v___x_716_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; uint8_t v___x_733_; 
lean_dec(v_id_604_);
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_733_ = l_Lean_Syntax_isOfKind(v_a_533_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v___x_729_);
goto v___jp_582_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_734_ = l_Lean_Syntax_getArgs(v___x_729_);
lean_dec(v___x_729_);
v___x_735_ = lean_array_get_size(v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_737_ = lean_nat_dec_lt(v___x_576_, v___x_735_);
if (v___x_737_ == 0)
{
lean_dec_ref(v___x_734_);
v_a_724_ = v___x_736_;
goto v___jp_723_;
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_735_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_731_, v___x_734_, v___x_738_, v___x_739_, v___x_736_, v_a_535_, v_a_536_);
lean_dec_ref(v___x_734_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v_a_724_ = v_a_741_;
goto v___jp_723_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_534_);
v_a_742_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_740_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_Syntax_getArg(v___x_729_, v___x_576_);
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_752_ = l_Lean_Syntax_isOfKind(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
lean_dec(v_id_604_);
v___x_753_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_754_ = l_Lean_Syntax_isOfKind(v_a_533_, v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v___x_729_);
goto v___jp_577_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_755_ = l_Lean_Syntax_getArgs(v___x_729_);
lean_dec(v___x_729_);
v___x_756_ = lean_array_get_size(v___x_755_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_758_ = lean_nat_dec_lt(v___x_576_, v___x_756_);
if (v___x_758_ == 0)
{
lean_dec_ref(v___x_755_);
v_a_718_ = v___x_757_;
goto v___jp_717_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_756_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_752_, v___x_755_, v___x_759_, v___x_760_, v___x_757_, v_a_535_, v_a_536_);
lean_dec_ref(v___x_755_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v_a_718_ = v_a_762_;
goto v___jp_717_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_534_);
v_a_763_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_dec(v___x_729_);
lean_dec(v_a_533_);
v___y_635_ = v_a_535_;
v___y_636_ = v_a_536_;
goto v___jp_634_;
}
}
}
else
{
lean_dec(v___x_729_);
lean_dec(v_a_533_);
v___y_635_ = v_a_535_;
v___y_636_ = v_a_536_;
goto v___jp_634_;
}
v___jp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_inc(v_id_604_);
v___x_637_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_637_, 0, v_id_604_);
v___x_638_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_637_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_707_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_707_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_707_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_707_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
if (lean_obj_tag(v_a_639_) == 1)
{
lean_object* v_val_643_; 
v_val_643_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v_a_639_, 1);
switch(lean_obj_tag(v_val_643_))
{
case 0:
{
lean_object* v_cat_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
lean_dec(v_id_604_);
v_cat_644_ = lean_ctor_get(v_val_643_, 0);
lean_inc(v_cat_644_);
lean_dec_ref_known(v_val_643_, 1);
v___x_645_ = lean_box(0);
v___x_646_ = l_Lean_Syntax_mkAntiquotNode(v_cat_644_, v_a_534_, v___x_576_, v___x_645_, v___x_542_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_646_);
v___x_648_ = v___x_641_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
case 1:
{
lean_object* v_decl_650_; 
lean_del_object(v___x_641_);
lean_dec(v_id_604_);
v_decl_650_ = lean_ctor_get(v_val_643_, 0);
lean_inc(v_decl_650_);
lean_dec_ref_known(v_val_643_, 1);
if (lean_obj_tag(v_decl_650_) == 1)
{
lean_object* v_pre_651_; 
v_pre_651_ = lean_ctor_get(v_decl_650_, 0);
if (lean_obj_tag(v_pre_651_) == 1)
{
lean_object* v_pre_652_; 
v_pre_652_ = lean_ctor_get(v_pre_651_, 0);
if (lean_obj_tag(v_pre_652_) == 1)
{
lean_object* v_pre_653_; 
v_pre_653_ = lean_ctor_get(v_pre_652_, 0);
switch(lean_obj_tag(v_pre_653_))
{
case 0:
{
lean_object* v_str_654_; lean_object* v_str_655_; lean_object* v_str_656_; uint8_t v___x_657_; 
v_str_654_ = lean_ctor_get(v_decl_650_, 1);
v_str_655_ = lean_ctor_get(v_pre_651_, 1);
v_str_656_ = lean_ctor_get(v_pre_652_, 1);
v___x_657_ = lean_string_dec_eq(v_str_656_, v___x_538_);
if (v___x_657_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_string_dec_eq(v_str_655_, v___x_539_);
if (v___x_658_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = lean_string_dec_eq(v_str_654_, v___x_605_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_661_ = lean_string_dec_eq(v_str_654_, v___x_660_);
if (v___x_661_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
lean_object* v___x_662_; 
lean_dec_ref_known(v_decl_650_, 2);
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_594_ = v___x_662_;
goto v___jp_593_;
}
}
else
{
lean_object* v___x_663_; 
lean_dec_ref_known(v_decl_650_, 2);
v___x_663_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_594_ = v___x_663_;
goto v___jp_593_;
}
}
}
}
case 1:
{
lean_object* v_pre_664_; 
v_pre_664_ = lean_ctor_get(v_pre_653_, 0);
if (lean_obj_tag(v_pre_664_) == 0)
{
lean_object* v_str_665_; lean_object* v_str_666_; lean_object* v_str_667_; lean_object* v_str_668_; uint8_t v___x_669_; 
v_str_665_ = lean_ctor_get(v_decl_650_, 1);
v_str_666_ = lean_ctor_get(v_pre_651_, 1);
v_str_667_ = lean_ctor_get(v_pre_652_, 1);
v_str_668_ = lean_ctor_get(v_pre_653_, 1);
v___x_669_ = lean_string_dec_eq(v_str_668_, v___x_538_);
if (v___x_669_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_string_dec_eq(v_str_667_, v___x_539_);
if (v___x_670_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_672_ = lean_string_dec_eq(v_str_666_, v___x_671_);
if (v___x_672_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_string_dec_eq(v_str_665_, v___x_605_);
if (v___x_673_ == 0)
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
else
{
lean_object* v___x_674_; 
lean_dec_ref_known(v_decl_650_, 2);
v___x_674_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_594_ = v___x_674_;
goto v___jp_593_;
}
}
}
}
}
else
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
}
default: 
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
}
}
else
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
}
else
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
}
else
{
v___y_594_ = v_decl_650_;
goto v___jp_593_;
}
}
default: 
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_641_);
v_isSharedCheck_699_ = !lean_is_exclusive(v_val_643_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_val_643_, 0);
lean_dec(v_unused_700_);
v___x_676_ = v_val_643_;
v_isShared_677_ = v_isSharedCheck_699_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_val_643_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_699_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_TSyntax_getId(v_id_604_);
lean_dec(v_id_604_);
v___x_679_ = l_Lean_Name_eraseMacroScopes(v___x_678_);
lean_dec(v___x_678_);
v___x_680_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_679_);
lean_dec(v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; 
lean_del_object(v___x_676_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
v___y_588_ = v___x_682_;
goto v___jp_587_;
}
else
{
lean_object* v_val_683_; 
v_val_683_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v_a_681_, 1);
v___y_588_ = v_val_683_;
goto v___jp_587_;
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_534_);
v_a_684_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_698_ == 0)
{
v___x_686_ = v___x_680_;
v_isShared_687_ = v_isSharedCheck_698_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_680_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_698_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_ref_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v_ref_688_ = lean_ctor_get(v___y_635_, 7);
v___x_689_ = lean_io_error_to_string(v_a_684_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 3);
lean_ctor_set(v___x_676_, 0, v___x_689_);
v___x_691_ = v___x_676_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_697_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_692_ = l_Lean_MessageData_ofFormat(v___x_691_);
lean_inc(v_ref_688_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_ref_688_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_693_);
v___x_695_ = v___x_686_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
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
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_del_object(v___x_641_);
lean_dec(v_a_639_);
lean_dec(v_a_534_);
v___x_701_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_702_ = l_Lean_MessageData_ofSyntax(v_id_604_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_705_, v___y_635_, v___y_636_);
return v___x_706_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_id_604_);
lean_dec(v_a_534_);
v_a_708_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_638_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_638_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_array_get_size(v_a_718_);
v___x_720_ = lean_nat_dec_eq(v___x_719_, v___x_716_);
if (v___x_720_ == 0)
{
lean_dec_ref(v_a_718_);
goto v___jp_577_;
}
else
{
lean_object* v___x_721_; 
v___x_721_ = lean_array_fget(v_a_718_, v___x_576_);
lean_dec_ref(v_a_718_);
v_a_533_ = v___x_721_;
goto _start;
}
}
v___jp_723_:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_array_get_size(v_a_724_);
v___x_726_ = lean_nat_dec_eq(v___x_725_, v___x_716_);
if (v___x_726_ == 0)
{
lean_dec_ref(v_a_724_);
goto v___jp_582_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_array_fget(v_a_724_, v___x_576_);
lean_dec_ref(v_a_724_);
v_a_533_ = v___x_727_;
goto _start;
}
}
}
v___jp_577_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_box(0);
v___x_580_ = l_Lean_Syntax_mkAntiquotNode(v___x_578_, v_a_534_, v___x_576_, v___x_579_, v___x_542_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
v___jp_582_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_box(0);
v___x_584_ = lean_box(0);
v___x_585_ = l_Lean_Syntax_mkAntiquotNode(v___x_583_, v_a_534_, v___x_576_, v___x_584_, v___x_542_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
v___jp_587_:
{
lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_box(0);
v___x_590_ = 0;
v___x_591_ = l_Lean_Syntax_mkAntiquotNode(v___y_588_, v_a_534_, v___x_576_, v___x_589_, v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
v___jp_593_:
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = lean_box(0);
v___x_596_ = 0;
v___x_597_ = l_Lean_Syntax_mkAntiquotNode(v___y_594_, v_a_534_, v___x_576_, v___x_595_, v___x_596_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
v___jp_599_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_box(0);
v___x_602_ = l_Lean_Syntax_mkAntiquotNode(v___x_600_, v_a_534_, v___x_576_, v___x_601_, v___x_542_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
v___jp_543_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_544_ = lean_box(0);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_box(0);
v___x_547_ = l_Lean_Syntax_mkAntiquotNode(v___x_544_, v_a_534_, v___x_545_, v___x_546_, v___x_542_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_777_, v___y_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_787_, lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_788_, v___y_789_, v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_793_, lean_object* v_msg_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_793_, v_msg_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_799_, lean_object* v_macroStack_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_799_, v_macroStack_800_, v___y_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_805_, lean_object* v_macroStack_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_805_, v_macroStack_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_814_, lean_object* v_stx_815_, lean_object* v_id_816_, lean_object* v_suffix_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_815_, v_id_816_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_836_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_836_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_826_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_814_, v_a_822_, v_suffix_817_);
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_mk_empty_array_with_capacity(v___x_827_);
v___x_829_ = lean_array_push(v___x_828_, v___x_826_);
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_831_ = lean_box(2);
v___x_832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
lean_ctor_set(v___x_832_, 2, v___x_829_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_832_);
v___x_834_ = v___x_824_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_dec_ref(v_suffix_817_);
lean_dec(v_kind_814_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_837_, lean_object* v_stx_838_, lean_object* v_id_839_, lean_object* v_suffix_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_837_, v_stx_838_, v_id_839_, v_suffix_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v_env_848_; lean_object* v___x_849_; lean_object* v_mainModule_850_; lean_object* v___x_851_; 
v___x_847_ = lean_st_ref_get(v___y_845_);
v_env_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc_ref(v_env_848_);
lean_dec(v___x_847_);
v___x_849_ = l_Lean_Environment_header(v_env_848_);
lean_dec_ref(v_env_848_);
v_mainModule_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_mainModule_850_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_mainModule_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_852_);
lean_dec(v___y_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_866_ = lean_panic_fn_borrowed(v___x_865_, v_msg_864_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = l_Lean_maxRecDepthErrorMessage;
v___x_873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_875_ = l_Lean_MessageData_ofFormat(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_877_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_878_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_876_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_879_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_ref_879_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_887_, lean_object* v_declName_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_891_; lean_object* v_env_892_; lean_object* v___x_893_; uint8_t v___x_894_; uint8_t v___x_895_; 
v___x_891_ = 0;
v_env_892_ = l_Lean_Environment_setExporting(v_env_887_, v___x_891_);
lean_inc(v_declName_888_);
v___x_893_ = l_Lean_mkPrivateName(v_env_892_, v_declName_888_);
v___x_894_ = 1;
lean_inc_ref(v_env_892_);
v___x_895_ = l_Lean_Environment_contains(v_env_892_, v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = l_Lean_privateToUserName(v_declName_888_);
v___x_897_ = l_Lean_Environment_contains(v_env_892_, v___x_896_, v___x_894_);
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___y_890_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v_env_892_);
lean_dec(v_declName_888_);
v___x_900_ = lean_box(v___x_895_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___y_890_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_902_, lean_object* v_declName_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_902_, v_declName_903_, v___y_904_, v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_906_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_907_, lean_object* v_i_908_, lean_object* v_k_909_){
_start:
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_array_get_size(v_keys_907_);
v___x_911_ = lean_nat_dec_lt(v_i_908_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec(v_i_908_);
return v___x_911_;
}
else
{
lean_object* v_k_x27_912_; uint8_t v___x_913_; 
v_k_x27_912_ = lean_array_fget_borrowed(v_keys_907_, v_i_908_);
v___x_913_ = l_Lean_instBEqExtraModUse_beq(v_k_909_, v_k_x27_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v_i_908_, v___x_914_);
lean_dec(v_i_908_);
v_i_908_ = v___x_915_;
goto _start;
}
else
{
lean_dec(v_i_908_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_917_, lean_object* v_i_918_, lean_object* v_k_919_){
_start:
{
uint8_t v_res_920_; lean_object* v_r_921_; 
v_res_920_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_917_, v_i_918_, v_k_919_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_keys_917_);
v_r_921_ = lean_box(v_res_920_);
return v_r_921_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_922_, size_t v_x_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v_es_925_; lean_object* v___x_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v_j_929_; lean_object* v___x_930_; 
v_es_925_ = lean_ctor_get(v_x_922_, 0);
v___x_926_ = lean_box(2);
v___x_927_ = ((size_t)31ULL);
v___x_928_ = lean_usize_land(v_x_923_, v___x_927_);
v_j_929_ = lean_usize_to_nat(v___x_928_);
v___x_930_ = lean_array_get_borrowed(v___x_926_, v_es_925_, v_j_929_);
lean_dec(v_j_929_);
switch(lean_obj_tag(v___x_930_))
{
case 0:
{
lean_object* v_key_931_; uint8_t v___x_932_; 
v_key_931_ = lean_ctor_get(v___x_930_, 0);
v___x_932_ = l_Lean_instBEqExtraModUse_beq(v_x_924_, v_key_931_);
return v___x_932_;
}
case 1:
{
lean_object* v_node_933_; size_t v___x_934_; size_t v___x_935_; 
v_node_933_ = lean_ctor_get(v___x_930_, 0);
v___x_934_ = ((size_t)5ULL);
v___x_935_ = lean_usize_shift_right(v_x_923_, v___x_934_);
v_x_922_ = v_node_933_;
v_x_923_ = v___x_935_;
goto _start;
}
default: 
{
uint8_t v___x_937_; 
v___x_937_ = 0;
return v___x_937_;
}
}
}
else
{
lean_object* v_ks_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_ks_938_ = lean_ctor_get(v_x_922_, 0);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_938_, v___x_939_, v_x_924_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
size_t v_x_42668__boxed_944_; uint8_t v_res_945_; lean_object* v_r_946_; 
v_x_42668__boxed_944_ = lean_unbox_usize(v_x_942_);
lean_dec(v_x_942_);
v_res_945_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_941_, v_x_42668__boxed_944_, v_x_943_);
lean_dec_ref(v_x_943_);
lean_dec_ref(v_x_941_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
uint64_t v___x_949_; size_t v___x_950_; uint8_t v___x_951_; 
v___x_949_ = l_Lean_instHashableExtraModUse_hash(v_x_948_);
v___x_950_ = lean_uint64_to_usize(v___x_949_);
v___x_951_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_947_, v___x_950_, v_x_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_952_, v_x_953_);
lean_dec_ref(v_x_953_);
lean_dec_ref(v_x_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_956_; double v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_float_of_nat(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_960_, lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Elab_Command_getRef___redArg(v___y_962_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1016_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_961_, v___y_963_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_1016_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1016_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v_traceState_973_; lean_object* v_env_974_; lean_object* v_messages_975_; lean_object* v_scopes_976_; lean_object* v_usedQuotCtxts_977_; lean_object* v_nextMacroScope_978_; lean_object* v_maxRecDepth_979_; lean_object* v_ngen_980_; lean_object* v_auxDeclNGen_981_; lean_object* v_infoState_982_; lean_object* v_snapshotTasks_983_; lean_object* v_prevLinterStates_984_; lean_object* v_codeQualityEntryTasks_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1015_; 
v___x_972_ = lean_st_ref_take(v___y_963_);
v_traceState_973_ = lean_ctor_get(v___x_972_, 9);
v_env_974_ = lean_ctor_get(v___x_972_, 0);
v_messages_975_ = lean_ctor_get(v___x_972_, 1);
v_scopes_976_ = lean_ctor_get(v___x_972_, 2);
v_usedQuotCtxts_977_ = lean_ctor_get(v___x_972_, 3);
v_nextMacroScope_978_ = lean_ctor_get(v___x_972_, 4);
v_maxRecDepth_979_ = lean_ctor_get(v___x_972_, 5);
v_ngen_980_ = lean_ctor_get(v___x_972_, 6);
v_auxDeclNGen_981_ = lean_ctor_get(v___x_972_, 7);
v_infoState_982_ = lean_ctor_get(v___x_972_, 8);
v_snapshotTasks_983_ = lean_ctor_get(v___x_972_, 10);
v_prevLinterStates_984_ = lean_ctor_get(v___x_972_, 11);
v_codeQualityEntryTasks_985_ = lean_ctor_get(v___x_972_, 12);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_987_ = v___x_972_;
v_isShared_988_ = v_isSharedCheck_1015_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_codeQualityEntryTasks_985_);
lean_inc(v_prevLinterStates_984_);
lean_inc(v_snapshotTasks_983_);
lean_inc(v_traceState_973_);
lean_inc(v_infoState_982_);
lean_inc(v_auxDeclNGen_981_);
lean_inc(v_ngen_980_);
lean_inc(v_maxRecDepth_979_);
lean_inc(v_nextMacroScope_978_);
lean_inc(v_usedQuotCtxts_977_);
lean_inc(v_scopes_976_);
lean_inc(v_messages_975_);
lean_inc(v_env_974_);
lean_dec(v___x_972_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1015_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint64_t v_tid_989_; lean_object* v_traces_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1014_; 
v_tid_989_ = lean_ctor_get_uint64(v_traceState_973_, sizeof(void*)*1);
v_traces_990_ = lean_ctor_get(v_traceState_973_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_traceState_973_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_992_ = v_traceState_973_;
v_isShared_993_ = v_isSharedCheck_1014_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_traces_990_);
lean_dec(v_traceState_973_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1014_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; double v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_994_ = lean_box(0);
v___x_995_ = lean_box(0);
v___x_996_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_997_ = 0;
v___x_998_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_999_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_999_, 0, v_cls_960_);
lean_ctor_set(v___x_999_, 1, v___x_995_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
lean_ctor_set_float(v___x_999_, sizeof(void*)*3, v___x_996_);
lean_ctor_set_float(v___x_999_, sizeof(void*)*3 + 8, v___x_996_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*3 + 16, v___x_997_);
v___x_1000_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_1001_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v_a_968_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_966_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_PersistentArray_push___redArg(v_traces_990_, v___x_1002_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1003_);
v___x_1005_ = v___x_992_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1003_);
lean_ctor_set_uint64(v_reuseFailAlloc_1013_, sizeof(void*)*1, v_tid_989_);
v___x_1005_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 9, v___x_1005_);
v___x_1007_ = v___x_987_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_env_974_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_messages_975_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_scopes_976_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_usedQuotCtxts_977_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_nextMacroScope_978_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_maxRecDepth_979_);
lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_ngen_980_);
lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_auxDeclNGen_981_);
lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_infoState_982_);
lean_ctor_set(v_reuseFailAlloc_1012_, 9, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1012_, 10, v_snapshotTasks_983_);
lean_ctor_set(v_reuseFailAlloc_1012_, 11, v_prevLinterStates_984_);
lean_ctor_set(v_reuseFailAlloc_1012_, 12, v_codeQualityEntryTasks_985_);
v___x_1007_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_st_ref_put(v___y_963_, v___x_1007_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_994_);
v___x_1010_ = v___x_970_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_994_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_msg_961_);
lean_dec(v_cls_960_);
v_a_1017_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_965_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_965_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1025_, v_msg_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0(lean_object* v___x_1031_, lean_object* v_entry_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v_addEntryFn_1034_; lean_object* v_importedEntries_1035_; lean_object* v_state_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_addEntryFn_1034_ = lean_ctor_get(v___x_1031_, 3);
lean_inc(v_addEntryFn_1034_);
lean_dec_ref(v___x_1031_);
v_importedEntries_1035_ = lean_ctor_get(v_s_1033_, 0);
v_state_1036_ = lean_ctor_get(v_s_1033_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_s_1033_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v_s_1033_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_state_1036_);
lean_inc(v_importedEntries_1035_);
lean_dec(v_s_1033_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_state_1040_; lean_object* v___x_1042_; 
v_state_1040_ = lean_apply_2(v_addEntryFn_1034_, v_state_1036_, v_entry_1032_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v_state_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_importedEntries_1035_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_state_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9(void){
_start:
{
lean_object* v_cls_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_cls_1058_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
v___x_1060_ = l_Lean_Name_append(v___x_1059_, v_cls_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1071_, uint8_t v_isMeta_1072_, lean_object* v_hint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_env_1098_; uint8_t v_isExporting_1099_; lean_object* v_entry_1100_; lean_object* v___x_1101_; lean_object* v_env_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1096_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0);
v___x_1097_ = lean_st_ref_get(v___y_1075_);
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1098_);
lean_dec(v___x_1097_);
v_isExporting_1099_ = lean_ctor_get_uint8(v_env_1098_, sizeof(void*)*13);
lean_dec_ref(v_env_1098_);
lean_inc(v_mod_1071_);
v_entry_1100_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1100_, 0, v_mod_1071_);
lean_ctor_set_uint8(v_entry_1100_, sizeof(void*)*1, v_isExporting_1099_);
lean_ctor_set_uint8(v_entry_1100_, sizeof(void*)*1 + 1, v_isMeta_1072_);
v___x_1101_ = lean_st_ref_get(v___y_1075_);
v_env_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1101_);
v___x_1103_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1104_ = lean_box(1);
v___x_1105_ = lean_box(0);
v___x_1106_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1096_, v___x_1103_, v_env_1102_, v___x_1104_, v___x_1105_);
v___x_1107_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1106_, v_entry_1100_);
lean_dec(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___f_1108_; uint8_t v___x_1109_; lean_object* v___y_1111_; lean_object* v_cls_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v_scopes_1158_; lean_object* v___x_1159_; lean_object* v_opts_1160_; uint8_t v_hasTrace_1161_; 
v___f_1108_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_1108_, 0, v___x_1103_);
lean_closure_set(v___f_1108_, 1, v_entry_1100_);
v___x_1109_ = 1;
v_cls_1133_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1134_ = l_Lean_inheritedTraceOptions;
v___x_1135_ = lean_st_ref_get(v___x_1134_);
v___x_1136_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1137_ = lean_st_ref_get(v___y_1075_);
v_scopes_1158_ = lean_ctor_get(v___x_1137_, 2);
lean_inc(v_scopes_1158_);
lean_dec(v___x_1137_);
v___x_1159_ = l_List_head_x21___redArg(v___x_1136_, v_scopes_1158_);
lean_dec(v_scopes_1158_);
v_opts_1160_ = lean_ctor_get(v___x_1159_, 1);
lean_inc_ref(v_opts_1160_);
lean_dec(v___x_1159_);
v_hasTrace_1161_ = lean_ctor_get_uint8(v_opts_1160_, sizeof(void*)*1);
if (v_hasTrace_1161_ == 0)
{
lean_dec_ref(v_opts_1160_);
lean_dec(v___x_1135_);
lean_dec(v_hint_1073_);
lean_dec(v_mod_1071_);
v___y_1111_ = v___y_1075_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9);
v___x_1163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1135_, v_opts_1160_, v___x_1162_);
lean_dec_ref(v_opts_1160_);
lean_dec(v___x_1135_);
if (v___x_1163_ == 0)
{
lean_dec(v_hint_1073_);
lean_dec(v_mod_1071_);
v___y_1111_ = v___y_1075_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1164_; lean_object* v___y_1166_; 
v___x_1164_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
if (v_isExporting_1099_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1166_ = v___x_1173_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1166_ = v___x_1174_;
goto v___jp_1165_;
}
v___jp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc_ref(v___y_1166_);
v___x_1167_ = l_Lean_stringToMessageData(v___y_1166_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1164_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
if (v_isMeta_1072_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___y_1144_ = v___x_1170_;
v___y_1145_ = v___x_1171_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15));
v___y_1144_ = v___x_1170_;
v___y_1145_ = v___x_1172_;
goto v___jp_1143_;
}
}
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v_toEnvExtension_1113_; lean_object* v_env_1114_; lean_object* v_messages_1115_; lean_object* v_scopes_1116_; lean_object* v_usedQuotCtxts_1117_; lean_object* v_nextMacroScope_1118_; lean_object* v_maxRecDepth_1119_; lean_object* v_ngen_1120_; lean_object* v_auxDeclNGen_1121_; lean_object* v_infoState_1122_; lean_object* v_traceState_1123_; lean_object* v_snapshotTasks_1124_; lean_object* v_prevLinterStates_1125_; lean_object* v_codeQualityEntryTasks_1126_; lean_object* v_asyncMode_1127_; uint8_t v_logWrites_1128_; lean_object* v___x_1129_; 
v___x_1112_ = lean_st_ref_take(v___y_1111_);
v_toEnvExtension_1113_ = lean_ctor_get(v___x_1103_, 0);
v_env_1114_ = lean_ctor_get(v___x_1112_, 0);
lean_inc_ref(v_env_1114_);
v_messages_1115_ = lean_ctor_get(v___x_1112_, 1);
lean_inc_ref(v_messages_1115_);
v_scopes_1116_ = lean_ctor_get(v___x_1112_, 2);
lean_inc(v_scopes_1116_);
v_usedQuotCtxts_1117_ = lean_ctor_get(v___x_1112_, 3);
lean_inc(v_usedQuotCtxts_1117_);
v_nextMacroScope_1118_ = lean_ctor_get(v___x_1112_, 4);
lean_inc(v_nextMacroScope_1118_);
v_maxRecDepth_1119_ = lean_ctor_get(v___x_1112_, 5);
lean_inc(v_maxRecDepth_1119_);
v_ngen_1120_ = lean_ctor_get(v___x_1112_, 6);
lean_inc_ref(v_ngen_1120_);
v_auxDeclNGen_1121_ = lean_ctor_get(v___x_1112_, 7);
lean_inc_ref(v_auxDeclNGen_1121_);
v_infoState_1122_ = lean_ctor_get(v___x_1112_, 8);
lean_inc_ref(v_infoState_1122_);
v_traceState_1123_ = lean_ctor_get(v___x_1112_, 9);
lean_inc_ref(v_traceState_1123_);
v_snapshotTasks_1124_ = lean_ctor_get(v___x_1112_, 10);
lean_inc_ref(v_snapshotTasks_1124_);
v_prevLinterStates_1125_ = lean_ctor_get(v___x_1112_, 11);
lean_inc(v_prevLinterStates_1125_);
v_codeQualityEntryTasks_1126_ = lean_ctor_get(v___x_1112_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1126_);
lean_dec(v___x_1112_);
v_asyncMode_1127_ = lean_ctor_get(v_toEnvExtension_1113_, 2);
v_logWrites_1128_ = lean_ctor_get_uint8(v_toEnvExtension_1113_, sizeof(void*)*6);
v___x_1129_ = lean_box(0);
if (v_logWrites_1128_ == 0)
{
lean_object* v___x_1130_; 
lean_inc_ref(v_toEnvExtension_1113_);
v___x_1130_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1113_, v_env_1114_, v___f_1108_, v_asyncMode_1127_, v___x_1105_, v___x_1109_);
v___y_1078_ = v___x_1129_;
v___y_1079_ = v_prevLinterStates_1125_;
v___y_1080_ = v_traceState_1123_;
v___y_1081_ = v_usedQuotCtxts_1117_;
v___y_1082_ = v_snapshotTasks_1124_;
v___y_1083_ = v_scopes_1116_;
v___y_1084_ = v___y_1111_;
v___y_1085_ = v_ngen_1120_;
v___y_1086_ = v_codeQualityEntryTasks_1126_;
v___y_1087_ = v_infoState_1122_;
v___y_1088_ = v_auxDeclNGen_1121_;
v___y_1089_ = v_messages_1115_;
v___y_1090_ = v_maxRecDepth_1119_;
v___y_1091_ = v_nextMacroScope_1118_;
v___y_1092_ = v___x_1130_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_inc_ref_n(v_toEnvExtension_1113_, 2);
v___x_1131_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1113_, v_env_1114_);
lean_dec_ref(v_env_1114_);
v___x_1132_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1113_, v___x_1131_, v___f_1108_, v_asyncMode_1127_, v___x_1105_, v___x_1109_);
v___y_1078_ = v___x_1129_;
v___y_1079_ = v_prevLinterStates_1125_;
v___y_1080_ = v_traceState_1123_;
v___y_1081_ = v_usedQuotCtxts_1117_;
v___y_1082_ = v_snapshotTasks_1124_;
v___y_1083_ = v_scopes_1116_;
v___y_1084_ = v___y_1111_;
v___y_1085_ = v_ngen_1120_;
v___y_1086_ = v_codeQualityEntryTasks_1126_;
v___y_1087_ = v_infoState_1122_;
v___y_1088_ = v_auxDeclNGen_1121_;
v___y_1089_ = v_messages_1115_;
v___y_1090_ = v_maxRecDepth_1119_;
v___y_1091_ = v_nextMacroScope_1118_;
v___y_1092_ = v___x_1132_;
goto v___jp_1077_;
}
}
v___jp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1139_);
lean_ctor_set(v___x_1141_, 1, v___y_1140_);
v___x_1142_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1133_, v___x_1141_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
v___y_1111_ = v___y_1075_;
goto v___jp_1110_;
}
else
{
lean_dec_ref(v___f_1108_);
return v___x_1142_;
}
}
v___jp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
lean_inc_ref(v___y_1145_);
v___x_1146_ = l_Lean_stringToMessageData(v___y_1145_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1144_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_ofName(v_mod_1071_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_Name_isAnonymous(v_hint_1073_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1154_ = l_Lean_MessageData_ofName(v_hint_1073_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___y_1139_ = v___x_1151_;
v___y_1140_ = v___x_1155_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_hint_1073_);
v___x_1156_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
v___y_1139_ = v___x_1151_;
v___y_1140_ = v___x_1157_;
goto v___jp_1138_;
}
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref_known(v_entry_1100_, 1);
lean_dec(v_hint_1073_);
lean_dec(v_mod_1071_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
v___jp_1077_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1093_, 0, v___y_1092_);
lean_ctor_set(v___x_1093_, 1, v___y_1089_);
lean_ctor_set(v___x_1093_, 2, v___y_1083_);
lean_ctor_set(v___x_1093_, 3, v___y_1081_);
lean_ctor_set(v___x_1093_, 4, v___y_1091_);
lean_ctor_set(v___x_1093_, 5, v___y_1090_);
lean_ctor_set(v___x_1093_, 6, v___y_1085_);
lean_ctor_set(v___x_1093_, 7, v___y_1088_);
lean_ctor_set(v___x_1093_, 8, v___y_1087_);
lean_ctor_set(v___x_1093_, 9, v___y_1080_);
lean_ctor_set(v___x_1093_, 10, v___y_1082_);
lean_ctor_set(v___x_1093_, 11, v___y_1079_);
lean_ctor_set(v___x_1093_, 12, v___y_1086_);
v___x_1094_ = lean_st_ref_put(v___y_1084_, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___y_1078_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1177_, lean_object* v_isMeta_1178_, lean_object* v_hint_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_isMeta_boxed_1183_; lean_object* v_res_1184_; 
v_isMeta_boxed_1183_ = lean_unbox(v_isMeta_1178_);
v_res_1184_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1177_, v_isMeta_boxed_1183_, v_hint_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1185_, lean_object* v_declName_1186_, lean_object* v_as_1187_, size_t v_sz_1188_, size_t v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_usize_dec_lt(v_i_1189_, v_sz_1188_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v_declName_1186_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1190_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v_modules_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v_toImport_1201_; lean_object* v_module_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1196_ = l_Lean_Environment_header(v___x_1185_);
v_modules_1197_ = lean_ctor_get(v___x_1196_, 3);
lean_inc_ref(v_modules_1197_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1199_ = lean_array_uget_borrowed(v_as_1187_, v_i_1189_);
v___x_1200_ = lean_array_get(v___x_1198_, v_modules_1197_, v_a_1199_);
lean_dec_ref(v_modules_1197_);
v_toImport_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_toImport_1201_);
lean_dec(v___x_1200_);
v_module_1202_ = lean_ctor_get(v_toImport_1201_, 0);
lean_inc(v_module_1202_);
lean_dec_ref(v_toImport_1201_);
v___x_1203_ = lean_box(0);
v___x_1204_ = 0;
lean_inc(v_declName_1186_);
v___x_1205_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1202_, v___x_1204_, v_declName_1186_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1205_) == 0)
{
size_t v___x_1206_; size_t v___x_1207_; 
lean_dec_ref_known(v___x_1205_, 1);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1189_, v___x_1206_);
v_i_1189_ = v___x_1207_;
v_b_1190_ = v___x_1203_;
goto _start;
}
else
{
lean_dec(v_declName_1186_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1209_, lean_object* v_declName_1210_, lean_object* v_as_1211_, lean_object* v_sz_1212_, lean_object* v_i_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
size_t v_sz_boxed_1218_; size_t v_i_boxed_1219_; lean_object* v_res_1220_; 
v_sz_boxed_1218_ = lean_unbox_usize(v_sz_1212_);
lean_dec(v_sz_1212_);
v_i_boxed_1219_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1209_, v_declName_1210_, v_as_1211_, v_sz_boxed_1218_, v_i_boxed_1219_, v_b_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v_as_1211_);
lean_dec_ref(v___x_1209_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_box(0);
return v___x_1223_;
}
else
{
lean_object* v_key_1224_; lean_object* v_value_1225_; lean_object* v_tail_1226_; uint8_t v___x_1227_; 
v_key_1224_ = lean_ctor_get(v_x_1222_, 0);
v_value_1225_ = lean_ctor_get(v_x_1222_, 1);
v_tail_1226_ = lean_ctor_get(v_x_1222_, 2);
v___x_1227_ = lean_name_eq(v_key_1224_, v_a_1221_);
if (v___x_1227_ == 0)
{
v_x_1222_ = v_tail_1226_;
goto _start;
}
else
{
lean_object* v___x_1229_; 
lean_inc(v_value_1225_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_value_1225_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1230_, lean_object* v_x_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1230_, v_x_1231_);
lean_dec(v_x_1231_);
lean_dec(v_a_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_buckets_1235_; lean_object* v___x_1236_; uint64_t v___y_1238_; 
v_buckets_1235_ = lean_ctor_get(v_m_1233_, 1);
v___x_1236_ = lean_array_get_size(v_buckets_1235_);
if (lean_obj_tag(v_a_1234_) == 0)
{
uint64_t v___x_1252_; 
v___x_1252_ = 1723ULL;
v___y_1238_ = v___x_1252_;
goto v___jp_1237_;
}
else
{
uint64_t v_hash_1253_; 
v_hash_1253_ = lean_ctor_get_uint64(v_a_1234_, sizeof(void*)*2);
v___y_1238_ = v_hash_1253_;
goto v___jp_1237_;
}
v___jp_1237_:
{
uint64_t v___x_1239_; uint64_t v___x_1240_; uint64_t v_fold_1241_; uint64_t v___x_1242_; uint64_t v___x_1243_; uint64_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1239_ = 32ULL;
v___x_1240_ = lean_uint64_shift_right(v___y_1238_, v___x_1239_);
v_fold_1241_ = lean_uint64_xor(v___y_1238_, v___x_1240_);
v___x_1242_ = 16ULL;
v___x_1243_ = lean_uint64_shift_right(v_fold_1241_, v___x_1242_);
v___x_1244_ = lean_uint64_xor(v_fold_1241_, v___x_1243_);
v___x_1245_ = lean_uint64_to_usize(v___x_1244_);
v___x_1246_ = lean_usize_of_nat(v___x_1236_);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_sub(v___x_1246_, v___x_1247_);
v___x_1249_ = lean_usize_land(v___x_1245_, v___x_1248_);
v___x_1250_ = lean_array_uget_borrowed(v_buckets_1235_, v___x_1249_);
v___x_1251_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1234_, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_m_1254_);
return v_res_1256_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1260_, uint8_t v_isMeta_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_env_1270_; lean_object* v___y_1272_; lean_object* v___x_1285_; 
v___x_1265_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0);
v___x_1266_ = lean_st_ref_get(v___y_1263_);
v_env_1270_ = lean_ctor_get(v___x_1266_, 0);
lean_inc_ref(v_env_1270_);
lean_dec(v___x_1266_);
v___x_1285_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1270_, v_declName_1260_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref(v_env_1270_);
lean_dec(v_declName_1260_);
goto v___jp_1267_;
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1287_; lean_object* v_modules_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_val_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = l_Lean_Environment_header(v_env_1270_);
v_modules_1288_ = lean_ctor_get(v___x_1287_, 3);
lean_inc_ref(v_modules_1288_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = lean_array_get_size(v_modules_1288_);
v___x_1290_ = lean_nat_dec_lt(v_val_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_dec_ref(v_modules_1288_);
lean_dec(v_val_1286_);
lean_dec_ref(v_env_1270_);
lean_dec(v_declName_1260_);
goto v___jp_1267_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___y_1294_; 
v___x_1291_ = lean_array_fget(v_modules_1288_, v_val_1286_);
lean_dec(v_val_1286_);
lean_dec_ref(v_modules_1288_);
v___x_1292_ = lean_st_ref_get(v___y_1263_);
if (v_isMeta_1261_ == 0)
{
lean_dec(v___x_1292_);
v___y_1294_ = v_isMeta_1261_;
goto v___jp_1293_;
}
else
{
lean_object* v_env_1305_; uint8_t v___x_1306_; 
v_env_1305_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_env_1305_);
lean_dec(v___x_1292_);
lean_inc(v_declName_1260_);
v___x_1306_ = l_Lean_isMarkedMeta(v_env_1305_, v_declName_1260_);
if (v___x_1306_ == 0)
{
v___y_1294_ = v_isMeta_1261_;
goto v___jp_1293_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = 0;
v___y_1294_ = v___x_1307_;
goto v___jp_1293_;
}
}
v___jp_1293_:
{
lean_object* v_toImport_1295_; lean_object* v_module_1296_; lean_object* v___x_1297_; 
v_toImport_1295_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref(v_toImport_1295_);
lean_dec(v___x_1291_);
v_module_1296_ = lean_ctor_get(v_toImport_1295_, 0);
lean_inc(v_module_1296_);
lean_dec_ref(v_toImport_1295_);
lean_inc(v_declName_1260_);
v___x_1297_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1296_, v___y_1294_, v_declName_1260_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref_known(v___x_1297_, 1);
v___x_1298_ = l_Lean_indirectModUseExt;
v___x_1299_ = lean_box(1);
v___x_1300_ = lean_box(0);
lean_inc_ref(v_env_1270_);
v___x_1301_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1265_, v___x_1298_, v_env_1270_, v___x_1299_, v___x_1300_);
v___x_1302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1301_, v_declName_1260_);
lean_dec(v___x_1301_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___y_1272_ = v___x_1303_;
goto v___jp_1271_;
}
else
{
lean_object* v_val_1304_; 
v_val_1304_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1302_, 1);
v___y_1272_ = v_val_1304_;
goto v___jp_1271_;
}
}
else
{
lean_dec_ref(v_env_1270_);
lean_dec(v_declName_1260_);
return v___x_1297_;
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
v___jp_1271_:
{
lean_object* v___x_1273_; size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = lean_box(0);
v_sz_1274_ = lean_array_size(v___y_1272_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1270_, v_declName_1260_, v___y_1272_, v_sz_1274_, v___x_1275_, v___x_1273_, v___y_1262_, v___y_1263_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_env_1270_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1276_, 0);
lean_dec(v_unused_1284_);
v___x_1278_ = v___x_1276_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_dec(v___x_1276_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1273_);
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1273_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
return v___x_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1308_, lean_object* v_isMeta_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_isMeta_boxed_1313_; lean_object* v_res_1314_; 
v_isMeta_boxed_1313_ = lean_unbox(v_isMeta_1309_);
v_res_1314_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1308_, v_isMeta_boxed_1313_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
if (lean_obj_tag(v_as_x27_1315_) == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_b_1316_);
return v___x_1320_;
}
else
{
lean_object* v_head_1321_; lean_object* v_tail_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; 
v_head_1321_ = lean_ctor_get(v_as_x27_1315_, 0);
v_tail_1322_ = lean_ctor_get(v_as_x27_1315_, 1);
v___x_1323_ = lean_box(0);
v___x_1324_ = 1;
lean_inc(v_head_1321_);
v___x_1325_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1321_, v___x_1324_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_dec_ref_known(v___x_1325_, 1);
v_as_x27_1315_ = v_tail_1322_;
v_b_1316_ = v___x_1323_;
goto _start;
}
else
{
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1327_, v_b_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_as_x27_1327_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1333_, lean_object* v_opts_1334_, lean_object* v_currNamespace_1335_, lean_object* v_openDecls_1336_, lean_object* v_n_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = l_Lean_ResolveName_resolveGlobalName(v_env_1333_, v_opts_1334_, v_currNamespace_1335_, v_openDecls_1336_, v_n_1337_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___y_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1342_, lean_object* v_opts_1343_, lean_object* v_currNamespace_1344_, lean_object* v_openDecls_1345_, lean_object* v_n_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1342_, v_opts_1343_, v_currNamespace_1344_, v_openDecls_1345_, v_n_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v_opts_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1350_, lean_object* v_msg_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Elab_Command_getRef___redArg(v___y_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v_fileName_1357_; lean_object* v_fileMap_1358_; lean_object* v_currRecDepth_1359_; lean_object* v_cmdPos_1360_; lean_object* v_macroStack_1361_; lean_object* v_quotContext_x3f_1362_; lean_object* v_currMacroScope_1363_; lean_object* v_snap_x3f_1364_; lean_object* v_cancelTk_x3f_1365_; uint8_t v_suppressElabErrors_1366_; uint8_t v_checkDeprecated_1367_; lean_object* v_ref_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v_fileName_1357_ = lean_ctor_get(v___y_1352_, 0);
v_fileMap_1358_ = lean_ctor_get(v___y_1352_, 1);
v_currRecDepth_1359_ = lean_ctor_get(v___y_1352_, 2);
v_cmdPos_1360_ = lean_ctor_get(v___y_1352_, 3);
v_macroStack_1361_ = lean_ctor_get(v___y_1352_, 4);
v_quotContext_x3f_1362_ = lean_ctor_get(v___y_1352_, 5);
v_currMacroScope_1363_ = lean_ctor_get(v___y_1352_, 6);
v_snap_x3f_1364_ = lean_ctor_get(v___y_1352_, 8);
v_cancelTk_x3f_1365_ = lean_ctor_get(v___y_1352_, 9);
v_suppressElabErrors_1366_ = lean_ctor_get_uint8(v___y_1352_, sizeof(void*)*10);
v_checkDeprecated_1367_ = lean_ctor_get_uint8(v___y_1352_, sizeof(void*)*10 + 1);
v_ref_1368_ = l_Lean_replaceRef(v_ref_1350_, v_a_1356_);
lean_dec(v_a_1356_);
lean_inc(v_cancelTk_x3f_1365_);
lean_inc(v_snap_x3f_1364_);
lean_inc(v_currMacroScope_1363_);
lean_inc(v_quotContext_x3f_1362_);
lean_inc(v_macroStack_1361_);
lean_inc(v_cmdPos_1360_);
lean_inc(v_currRecDepth_1359_);
lean_inc_ref(v_fileMap_1358_);
lean_inc_ref(v_fileName_1357_);
v___x_1369_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1369_, 0, v_fileName_1357_);
lean_ctor_set(v___x_1369_, 1, v_fileMap_1358_);
lean_ctor_set(v___x_1369_, 2, v_currRecDepth_1359_);
lean_ctor_set(v___x_1369_, 3, v_cmdPos_1360_);
lean_ctor_set(v___x_1369_, 4, v_macroStack_1361_);
lean_ctor_set(v___x_1369_, 5, v_quotContext_x3f_1362_);
lean_ctor_set(v___x_1369_, 6, v_currMacroScope_1363_);
lean_ctor_set(v___x_1369_, 7, v_ref_1368_);
lean_ctor_set(v___x_1369_, 8, v_snap_x3f_1364_);
lean_ctor_set(v___x_1369_, 9, v_cancelTk_x3f_1365_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*10, v_suppressElabErrors_1366_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*10 + 1, v_checkDeprecated_1367_);
v___x_1370_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1351_, v___x_1369_, v___y_1353_);
lean_dec_ref_known(v___x_1369_, 10);
return v___x_1370_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_msg_1351_);
v_a_1371_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1355_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1355_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1379_, lean_object* v_msg_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1379_, v_msg_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_ref_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_env_1385_, lean_object* v_currNamespace_1386_, lean_object* v_openDecls_1387_, lean_object* v_n_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = l_Lean_ResolveName_resolveNamespace(v_env_1385_, v_currNamespace_1386_, v_openDecls_1387_, v_n_1388_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___y_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_env_1393_, lean_object* v_currNamespace_1394_, lean_object* v_openDecls_1395_, lean_object* v_n_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_env_1393_, v_currNamespace_1394_, v_openDecls_1395_, v_n_1396_, v___y_1397_, v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_currNamespace_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_currNamespace_1400_);
lean_ctor_set(v___x_1403_, 1, v___y_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_currNamespace_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_currNamespace_1404_, v___y_1405_, v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1408_, lean_object* v___y_1409_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v_x_1408_, 0);
lean_inc(v_a_1410_);
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_a_1410_);
lean_ctor_set(v___x_1411_, 1, v___y_1409_);
return v___x_1411_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v_x_1408_, 0);
lean_inc(v_a_1412_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_a_1412_);
lean_ctor_set(v___x_1413_, 1, v___y_1409_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1414_, v___y_1415_);
lean_dec_ref(v_x_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1417_, lean_object* v_stx_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1417_, v_stx_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
v_a_1423_ = lean_ctor_get(v___x_1421_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1421_, 0);
lean_dec(v_unused_1432_);
v___x_1425_ = v___x_1421_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1421_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_box(0);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_a_1423_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1461_; 
v_val_1433_ = lean_ctor_get(v_a_1422_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_a_1422_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1435_ = v_a_1422_;
v_isShared_1436_ = v_isSharedCheck_1461_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v_a_1422_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1461_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_snd_1437_; 
v_snd_1437_ = lean_ctor_get(v_val_1433_, 1);
lean_inc(v_snd_1437_);
lean_dec(v_val_1433_);
if (lean_obj_tag(v_snd_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
lean_del_object(v___x_1435_);
v_a_1438_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1421_, 2);
v_a_1439_ = lean_ctor_get(v_snd_1437_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_snd_1437_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v_snd_1437_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_snd_1437_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1444_, v_a_1438_);
lean_dec_ref(v___x_1444_);
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_a_1448_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1421_, 2);
v_a_1449_ = lean_ctor_get(v_snd_1437_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_snd_1437_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_snd_1437_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v_snd_1437_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_a_1449_);
v___x_1454_ = v___x_1435_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1456_, v_a_1448_);
lean_dec_ref(v___x_1456_);
return v___x_1457_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1462_ = lean_ctor_get(v___x_1421_, 0);
v_a_1463_ = lean_ctor_get(v___x_1421_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1421_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_inc(v_a_1462_);
lean_dec(v___x_1421_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
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
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1462_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1471_, lean_object* v_stx_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1471_, v_stx_1472_, v___y_1473_, v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
if (lean_obj_tag(v_as_1484_) == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v_head_1490_; lean_object* v_tail_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_scopes_1498_; lean_object* v___x_1499_; lean_object* v_opts_1500_; uint8_t v_hasTrace_1501_; 
v_head_1490_ = lean_ctor_get(v_as_1484_, 0);
lean_inc(v_head_1490_);
v_tail_1491_ = lean_ctor_get(v_as_1484_, 1);
lean_inc(v_tail_1491_);
lean_dec_ref_known(v_as_1484_, 2);
v_fst_1492_ = lean_ctor_get(v_head_1490_, 0);
lean_inc(v_fst_1492_);
v_snd_1493_ = lean_ctor_get(v_head_1490_, 1);
lean_inc(v_snd_1493_);
lean_dec(v_head_1490_);
v___x_1494_ = l_Lean_inheritedTraceOptions;
v___x_1495_ = lean_st_ref_get(v___x_1494_);
v___x_1496_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1497_ = lean_st_ref_get(v___y_1486_);
v_scopes_1498_ = lean_ctor_get(v___x_1497_, 2);
lean_inc(v_scopes_1498_);
lean_dec(v___x_1497_);
v___x_1499_ = l_List_head_x21___redArg(v___x_1496_, v_scopes_1498_);
lean_dec(v_scopes_1498_);
v_opts_1500_ = lean_ctor_get(v___x_1499_, 1);
lean_inc_ref(v_opts_1500_);
lean_dec(v___x_1499_);
v_hasTrace_1501_ = lean_ctor_get_uint8(v_opts_1500_, sizeof(void*)*1);
if (v_hasTrace_1501_ == 0)
{
lean_dec_ref(v_opts_1500_);
lean_dec(v___x_1495_);
lean_dec(v_snd_1493_);
lean_dec(v_fst_1492_);
v_as_1484_ = v_tail_1491_;
goto _start;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
lean_inc(v_fst_1492_);
v___x_1504_ = l_Lean_Name_append(v___x_1503_, v_fst_1492_);
v___x_1505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1495_, v_opts_1500_, v___x_1504_);
lean_dec(v___x_1504_);
lean_dec_ref(v_opts_1500_);
lean_dec(v___x_1495_);
if (v___x_1505_ == 0)
{
lean_dec(v_snd_1493_);
lean_dec(v_fst_1492_);
v_as_1484_ = v_tail_1491_;
goto _start;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_snd_1493_);
v___x_1508_ = l_Lean_MessageData_ofFormat(v___x_1507_);
v___x_1509_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1492_, v___x_1508_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref_known(v___x_1509_, 1);
v_as_1484_ = v_tail_1491_;
goto _start;
}
else
{
lean_dec(v_tail_1491_);
return v___x_1509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v_env_1522_; lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_scopes_1527_; lean_object* v___x_1528_; lean_object* v_opts_1529_; lean_object* v___x_1530_; 
v___x_1521_ = lean_st_ref_get(v___y_1519_);
v_env_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc_ref_n(v_env_1522_, 3);
lean_dec(v___x_1521_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1523_, 0, v_env_1522_);
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1524_, 0, v_env_1522_);
v___x_1525_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1526_ = lean_st_ref_get(v___y_1519_);
v_scopes_1527_ = lean_ctor_get(v___x_1526_, 2);
lean_inc(v_scopes_1527_);
lean_dec(v___x_1526_);
v___x_1528_ = l_List_head_x21___redArg(v___x_1525_, v_scopes_1527_);
lean_dec(v_scopes_1527_);
v_opts_1529_ = lean_ctor_get(v___x_1528_, 1);
lean_inc_ref(v_opts_1529_);
lean_dec(v___x_1528_);
v___x_1530_ = l_Lean_Elab_Command_getScope___redArg(v___y_1519_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_currNamespace_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_currNamespace_1532_ = lean_ctor_get(v_a_1531_, 2);
lean_inc_n(v_currNamespace_1532_, 2);
lean_dec(v_a_1531_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1533_, 0, v_currNamespace_1532_);
v___x_1534_ = l_Lean_Elab_Command_getScope___redArg(v___y_1519_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_openDecls_1536_; lean_object* v___f_1537_; lean_object* v___f_1538_; lean_object* v_methods_1539_; lean_object* v___x_1540_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v_openDecls_1536_ = lean_ctor_get(v_a_1535_, 3);
lean_inc_n(v_openDecls_1536_, 2);
lean_dec(v_a_1535_);
lean_inc(v_currNamespace_1532_);
lean_inc_ref(v_env_1522_);
v___f_1537_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1537_, 0, v_env_1522_);
lean_closure_set(v___f_1537_, 1, v_currNamespace_1532_);
lean_closure_set(v___f_1537_, 2, v_openDecls_1536_);
v___f_1538_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1538_, 0, v_env_1522_);
lean_closure_set(v___f_1538_, 1, v_opts_1529_);
lean_closure_set(v___f_1538_, 2, v_currNamespace_1532_);
lean_closure_set(v___f_1538_, 3, v_openDecls_1536_);
v_methods_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1539_, 0, v___f_1524_);
lean_ctor_set(v_methods_1539_, 1, v___f_1533_);
lean_ctor_set(v_methods_1539_, 2, v___f_1523_);
lean_ctor_set(v_methods_1539_, 3, v___f_1537_);
lean_ctor_set(v_methods_1539_, 4, v___f_1538_);
v___x_1540_ = l_Lean_Elab_Command_getRef___redArg(v___y_1518_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1518_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_currRecDepth_1544_; lean_object* v_quotContext_x3f_1545_; lean_object* v_a_1547_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_currRecDepth_1544_ = lean_ctor_get(v___y_1518_, 2);
v_quotContext_x3f_1545_ = lean_ctor_get(v___y_1518_, 5);
if (lean_obj_tag(v_quotContext_x3f_1545_) == 0)
{
lean_object* v___x_1621_; lean_object* v_a_1622_; 
v___x_1621_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1519_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
v_a_1547_ = v_a_1622_;
goto v___jp_1546_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v_quotContext_x3f_1545_, 0);
lean_inc(v_val_1623_);
v_a_1547_ = v_val_1623_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v_maxRecDepth_1549_; lean_object* v___x_1550_; lean_object* v_nextMacroScope_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1548_ = lean_st_ref_get(v___y_1519_);
v_maxRecDepth_1549_ = lean_ctor_get(v___x_1548_, 5);
lean_inc(v_maxRecDepth_1549_);
lean_dec(v___x_1548_);
v___x_1550_ = lean_st_ref_get(v___y_1519_);
v_nextMacroScope_1551_ = lean_ctor_get(v___x_1550_, 4);
lean_inc(v_nextMacroScope_1551_);
lean_dec(v___x_1550_);
lean_inc(v_currRecDepth_1544_);
v___x_1552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1552_, 0, v_methods_1539_);
lean_ctor_set(v___x_1552_, 1, v_a_1547_);
lean_ctor_set(v___x_1552_, 2, v_a_1543_);
lean_ctor_set(v___x_1552_, 3, v_currRecDepth_1544_);
lean_ctor_set(v___x_1552_, 4, v_maxRecDepth_1549_);
lean_ctor_set(v___x_1552_, 5, v_a_1541_);
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1554_, 0, v_nextMacroScope_1551_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
lean_ctor_set(v___x_1554_, 2, v___x_1553_);
v___x_1555_ = lean_apply_2(v_x_1517_, v___x_1552_, v___x_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v_a_1557_; lean_object* v_macroScope_1558_; lean_object* v_traceMsgs_1559_; lean_object* v_expandedMacroDecls_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 1);
lean_inc(v_a_1556_);
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1555_, 2);
v_macroScope_1558_ = lean_ctor_get(v_a_1556_, 0);
lean_inc(v_macroScope_1558_);
v_traceMsgs_1559_ = lean_ctor_get(v_a_1556_, 1);
lean_inc(v_traceMsgs_1559_);
v_expandedMacroDecls_1560_ = lean_ctor_get(v_a_1556_, 2);
lean_inc(v_expandedMacroDecls_1560_);
lean_dec(v_a_1556_);
v___x_1561_ = lean_box(0);
v___x_1562_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1560_, v___x_1561_, v___y_1518_, v___y_1519_);
lean_dec(v_expandedMacroDecls_1560_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; lean_object* v_env_1564_; lean_object* v_messages_1565_; lean_object* v_scopes_1566_; lean_object* v_usedQuotCtxts_1567_; lean_object* v_maxRecDepth_1568_; lean_object* v_ngen_1569_; lean_object* v_auxDeclNGen_1570_; lean_object* v_infoState_1571_; lean_object* v_traceState_1572_; lean_object* v_snapshotTasks_1573_; lean_object* v_prevLinterStates_1574_; lean_object* v_codeQualityEntryTasks_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref_known(v___x_1562_, 1);
v___x_1563_ = lean_st_ref_take(v___y_1519_);
v_env_1564_ = lean_ctor_get(v___x_1563_, 0);
v_messages_1565_ = lean_ctor_get(v___x_1563_, 1);
v_scopes_1566_ = lean_ctor_get(v___x_1563_, 2);
v_usedQuotCtxts_1567_ = lean_ctor_get(v___x_1563_, 3);
v_maxRecDepth_1568_ = lean_ctor_get(v___x_1563_, 5);
v_ngen_1569_ = lean_ctor_get(v___x_1563_, 6);
v_auxDeclNGen_1570_ = lean_ctor_get(v___x_1563_, 7);
v_infoState_1571_ = lean_ctor_get(v___x_1563_, 8);
v_traceState_1572_ = lean_ctor_get(v___x_1563_, 9);
v_snapshotTasks_1573_ = lean_ctor_get(v___x_1563_, 10);
v_prevLinterStates_1574_ = lean_ctor_get(v___x_1563_, 11);
v_codeQualityEntryTasks_1575_ = lean_ctor_get(v___x_1563_, 12);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1563_, 4);
lean_dec(v_unused_1602_);
v___x_1577_ = v___x_1563_;
v_isShared_1578_ = v_isSharedCheck_1601_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1575_);
lean_inc(v_prevLinterStates_1574_);
lean_inc(v_snapshotTasks_1573_);
lean_inc(v_traceState_1572_);
lean_inc(v_infoState_1571_);
lean_inc(v_auxDeclNGen_1570_);
lean_inc(v_ngen_1569_);
lean_inc(v_maxRecDepth_1568_);
lean_inc(v_usedQuotCtxts_1567_);
lean_inc(v_scopes_1566_);
lean_inc(v_messages_1565_);
lean_inc(v_env_1564_);
lean_dec(v___x_1563_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1601_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v_macroScope_1558_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_env_1564_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_messages_1565_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_scopes_1566_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_usedQuotCtxts_1567_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_macroScope_1558_);
lean_ctor_set(v_reuseFailAlloc_1600_, 5, v_maxRecDepth_1568_);
lean_ctor_set(v_reuseFailAlloc_1600_, 6, v_ngen_1569_);
lean_ctor_set(v_reuseFailAlloc_1600_, 7, v_auxDeclNGen_1570_);
lean_ctor_set(v_reuseFailAlloc_1600_, 8, v_infoState_1571_);
lean_ctor_set(v_reuseFailAlloc_1600_, 9, v_traceState_1572_);
lean_ctor_set(v_reuseFailAlloc_1600_, 10, v_snapshotTasks_1573_);
lean_ctor_set(v_reuseFailAlloc_1600_, 11, v_prevLinterStates_1574_);
lean_ctor_set(v_reuseFailAlloc_1600_, 12, v_codeQualityEntryTasks_1575_);
v___x_1580_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_st_ref_put(v___y_1519_, v___x_1580_);
v___x_1582_ = l_List_reverse___redArg(v_traceMsgs_1559_);
v___x_1583_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1582_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1583_, 0);
lean_dec(v_unused_1591_);
v___x_1585_ = v___x_1583_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v___x_1583_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v_a_1557_);
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1557_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_a_1557_);
v_a_1592_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1583_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1583_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_traceMsgs_1559_);
lean_dec(v_macroScope_1558_);
lean_dec(v_a_1557_);
v_a_1603_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1562_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1562_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1611_; 
v_a_1611_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1555_, 2);
if (lean_obj_tag(v_a_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v_a_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_a_1612_ = lean_ctor_get(v_a_1611_, 0);
lean_inc(v_a_1612_);
v_a_1613_ = lean_ctor_get(v_a_1611_, 1);
lean_inc_ref(v_a_1613_);
lean_dec_ref_known(v_a_1611_, 2);
v___x_1614_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1615_ = lean_string_dec_eq(v_a_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1613_);
v___x_1617_ = l_Lean_MessageData_ofFormat(v___x_1616_);
v___x_1618_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1612_, v___x_1617_, v___y_1518_, v___y_1519_);
lean_dec(v_a_1612_);
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; 
lean_dec_ref(v_a_1613_);
v___x_1619_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1612_);
return v___x_1619_;
}
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1541_);
lean_dec_ref_known(v_methods_1539_, 5);
lean_dec_ref(v_x_1517_);
v_a_1624_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1542_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1542_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref_known(v_methods_1539_, 5);
lean_dec_ref(v_x_1517_);
v_a_1632_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1540_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1540_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___f_1533_);
lean_dec(v_currNamespace_1532_);
lean_dec_ref(v_opts_1529_);
lean_dec_ref(v___f_1524_);
lean_dec_ref(v___f_1523_);
lean_dec_ref(v_env_1522_);
lean_dec_ref(v_x_1517_);
v_a_1640_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1534_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1534_);
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
lean_dec_ref(v_opts_1529_);
lean_dec_ref(v___f_1524_);
lean_dec_ref(v___f_1523_);
lean_dec_ref(v_env_1522_);
lean_dec_ref(v_x_1517_);
v_a_1648_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1530_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1530_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1660_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1675_ = l_String_toRawSubstring_x27(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1699_ = lean_unsigned_to_nat(14u);
v___x_1700_ = lean_unsigned_to_nat(22u);
v___x_1701_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1702_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1703_ = l_mkPanicMessageWithDecl(v___x_1702_, v___x_1701_, v___x_1700_, v___x_1699_, v___x_1698_);
return v___x_1703_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1720_ = l_String_toRawSubstring_x27(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1733_ = l_Lean_mkAtom(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1736_ = l_Lean_mkAtom(v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1737_, lean_object* v_id_1738_, lean_object* v_stx_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_pat_1744_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1739_);
v___x_1748_ = l_Lean_Syntax_isOfKind(v_stx_1739_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1739_);
v___x_1750_ = l_Lean_Syntax_isOfKind(v_stx_1739_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v_a_1757_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v_a_1793_; uint8_t v___x_1824_; 
v___x_1751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1739_);
v___x_1824_ = l_Lean_Syntax_isOfKind(v_stx_1739_, v___x_1751_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1739_);
v___x_1826_ = l_Lean_Syntax_isOfKind(v_stx_1739_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1739_);
v___x_1828_ = l_Lean_Syntax_isOfKind(v_stx_1739_, v___x_1827_);
if (v___x_1828_ == 0)
{
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = l_Lean_SourceInfo_fromRef(v_a_1830_, v___x_1828_);
lean_dec(v_a_1830_);
v___x_1832_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v_a_1835_; lean_object* v_quotContext_x3f_1866_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v_quotContext_x3f_1866_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_1866_) == 0)
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v_a_1835_ = v_a_1868_;
goto v___jp_1834_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1833_);
lean_dec(v___x_1831_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_1869_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v_quotContext_x3f_1866_, 0);
lean_inc(v_val_1877_);
v_a_1835_ = v_val_1877_;
goto v___jp_1834_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1836_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1837_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1838_ = l_Lean_addMacroScope(v_a_1835_, v___x_1837_, v_a_1833_);
v___x_1839_ = lean_box(0);
lean_inc_n(v___x_1831_, 4);
v___x_1840_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1831_);
lean_ctor_set(v___x_1840_, 1, v___x_1836_);
lean_ctor_set(v___x_1840_, 2, v___x_1838_);
lean_ctor_set(v___x_1840_, 3, v___x_1839_);
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1831_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_1844_ = l_Lean_Syntax_node1(v___x_1831_, v___x_1843_, v_stx_1739_);
v___x_1845_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1831_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_Syntax_node4(v___x_1831_, v___x_1751_, v___x_1840_, v___x_1842_, v___x_1844_, v___x_1846_);
v___x_1848_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1847_);
lean_ctor_set(v___x_1853_, 1, v_a_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v___x_1847_);
v_a_1858_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1848_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1848_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v___x_1831_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_1878_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1832_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1832_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_1886_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1829_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1829_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_val_1894_; lean_object* v___x_1895_; 
lean_dec(v_id_1738_);
v_val_1894_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_1895_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_1894_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v_pat_1744_ = v_a_1896_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_stx_1739_);
v_a_1897_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1895_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1895_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_1905_);
lean_inc(v___x_1906_);
v___x_1907_ = l_Lean_Syntax_matchesNull(v___x_1906_, v___x_1905_);
if (v___x_1907_ == 0)
{
lean_dec(v___x_1906_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = l_Lean_SourceInfo_fromRef(v_a_1909_, v___x_1907_);
lean_dec(v_a_1909_);
v___x_1911_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_a_1914_; lean_object* v_quotContext_x3f_1945_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v_quotContext_x3f_1945_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_1945_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_a_1914_ = v_a_1947_;
goto v___jp_1913_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_a_1912_);
lean_dec(v___x_1910_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_1948_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_val_1956_; 
v_val_1956_ = lean_ctor_get(v_quotContext_x3f_1945_, 0);
lean_inc(v_val_1956_);
v_a_1914_ = v_val_1956_;
goto v___jp_1913_;
}
v___jp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1916_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1917_ = l_Lean_addMacroScope(v_a_1914_, v___x_1916_, v_a_1912_);
v___x_1918_ = lean_box(0);
lean_inc_n(v___x_1910_, 4);
v___x_1919_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1910_);
lean_ctor_set(v___x_1919_, 1, v___x_1915_);
lean_ctor_set(v___x_1919_, 2, v___x_1917_);
lean_ctor_set(v___x_1919_, 3, v___x_1918_);
v___x_1920_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1910_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_1923_ = l_Lean_Syntax_node1(v___x_1910_, v___x_1922_, v_stx_1739_);
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1910_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_Syntax_node4(v___x_1910_, v___x_1751_, v___x_1919_, v___x_1921_, v___x_1923_, v___x_1925_);
v___x_1927_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1936_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1926_);
lean_ctor_set(v___x_1932_, 1, v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v___x_1926_);
v_a_1937_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1927_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v___x_1910_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_1957_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1911_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1911_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_1965_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1908_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1908_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_val_1973_; lean_object* v___x_1974_; 
lean_dec(v_id_1738_);
v_val_1973_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_1973_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_1974_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_1973_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v_pat_1744_ = v_a_1975_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v_stx_1739_);
v_a_1976_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1974_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1974_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1984_ = lean_unsigned_to_nat(3u);
v___x_1985_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_1984_);
v___x_1986_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_1985_);
v___x_1987_ = l_Lean_Syntax_isOfKind(v___x_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_dec(v___x_1985_);
lean_dec(v___x_1906_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_SourceInfo_fromRef(v_a_1989_, v___x_1826_);
lean_dec(v_a_1989_);
v___x_1991_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v_a_1994_; lean_object* v_quotContext_x3f_2025_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v_quotContext_x3f_2025_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2025_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v_a_1994_ = v_a_2027_;
goto v___jp_1993_;
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_a_1992_);
lean_dec(v___x_1990_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2028_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_val_2036_; 
v_val_2036_ = lean_ctor_get(v_quotContext_x3f_2025_, 0);
lean_inc(v_val_2036_);
v_a_1994_ = v_val_2036_;
goto v___jp_1993_;
}
v___jp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_1995_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1996_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1997_ = l_Lean_addMacroScope(v_a_1994_, v___x_1996_, v_a_1992_);
v___x_1998_ = lean_box(0);
lean_inc_n(v___x_1990_, 4);
v___x_1999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1990_);
lean_ctor_set(v___x_1999_, 1, v___x_1995_);
lean_ctor_set(v___x_1999_, 2, v___x_1997_);
lean_ctor_set(v___x_1999_, 3, v___x_1998_);
v___x_2000_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1990_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2003_ = l_Lean_Syntax_node1(v___x_1990_, v___x_2002_, v_stx_1739_);
v___x_2004_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_1990_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = l_Lean_Syntax_node4(v___x_1990_, v___x_1751_, v___x_1999_, v___x_2001_, v___x_2003_, v___x_2005_);
v___x_2007_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2006_);
lean_ctor_set(v___x_2012_, 1, v_a_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v___x_2006_);
v_a_2017_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2007_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2007_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v___x_1990_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2037_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1991_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1991_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2045_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_1988_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_1988_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_val_2053_; lean_object* v___x_2054_; 
lean_dec(v_id_1738_);
v_val_2053_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2053_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2054_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2053_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v_pat_1744_ = v_a_2055_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_stx_1739_);
v_a_2056_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2054_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2054_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_object* v___x_2064_; lean_object* v_stx_2065_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___x_2091_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v_stx_2065_ = l_Lean_Syntax_getArg(v___x_1906_, v___x_2064_);
lean_dec(v___x_1906_);
v___x_2091_ = lean_unsigned_to_nat(2u);
v___x_2144_ = lean_unsigned_to_nat(4u);
v___x_2145_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2144_);
v___x_2146_ = l_Lean_Syntax_isNone(v___x_2145_);
if (v___x_2146_ == 0)
{
uint8_t v___x_2147_; 
lean_inc(v___x_2145_);
v___x_2147_ = l_Lean_Syntax_matchesNull(v___x_2145_, v___x_2091_);
if (v___x_2147_ == 0)
{
lean_dec(v___x_2145_);
lean_dec(v_stx_2065_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = l_Lean_SourceInfo_fromRef(v_a_2149_, v___x_2147_);
lean_dec(v_a_2149_);
v___x_2151_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v_a_2154_; lean_object* v_quotContext_x3f_2185_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v_quotContext_x3f_2185_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2185_) == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_a_2154_ = v_a_2187_;
goto v___jp_2153_;
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2152_);
lean_dec(v___x_2150_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2188_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2186_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2186_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_val_2196_; 
v_val_2196_ = lean_ctor_get(v_quotContext_x3f_2185_, 0);
lean_inc(v_val_2196_);
v_a_2154_ = v_val_2196_;
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2155_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2156_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2157_ = l_Lean_addMacroScope(v_a_2154_, v___x_2156_, v_a_2152_);
v___x_2158_ = lean_box(0);
lean_inc_n(v___x_2150_, 4);
v___x_2159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2150_);
lean_ctor_set(v___x_2159_, 1, v___x_2155_);
lean_ctor_set(v___x_2159_, 2, v___x_2157_);
lean_ctor_set(v___x_2159_, 3, v___x_2158_);
v___x_2160_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2150_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2163_ = l_Lean_Syntax_node1(v___x_2150_, v___x_2162_, v_stx_1739_);
v___x_2164_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2150_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_Syntax_node4(v___x_2150_, v___x_1751_, v___x_2159_, v___x_2161_, v___x_2163_, v___x_2165_);
v___x_2167_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2176_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2166_);
lean_ctor_set(v___x_2172_, 1, v_a_2168_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2172_);
v___x_2174_ = v___x_2170_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v___x_2166_);
v_a_2177_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2167_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2167_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v___x_2150_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2197_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2151_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2151_);
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
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2205_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2148_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2148_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_val_2213_; lean_object* v___x_2214_; 
lean_dec(v_id_1738_);
v_val_2213_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2214_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2213_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v_pat_1744_ = v_a_2215_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_stx_1739_);
v_a_2216_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2214_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2214_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = l_Lean_Syntax_getArg(v___x_2145_, v___x_1905_);
lean_dec(v___x_2145_);
v___x_2225_ = l_Lean_Syntax_matchesNull(v___x_2224_, v___x_1905_);
if (v___x_2225_ == 0)
{
lean_dec(v_stx_2065_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = l_Lean_SourceInfo_fromRef(v_a_2227_, v___x_2225_);
lean_dec(v_a_2227_);
v___x_2229_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v_a_2232_; lean_object* v_quotContext_x3f_2263_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v_quotContext_x3f_2263_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2263_) == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v_a_2232_ = v_a_2265_;
goto v___jp_2231_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2230_);
lean_dec(v___x_2228_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
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
else
{
lean_object* v_val_2274_; 
v_val_2274_ = lean_ctor_get(v_quotContext_x3f_2263_, 0);
lean_inc(v_val_2274_);
v_a_2232_ = v_val_2274_;
goto v___jp_2231_;
}
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2234_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2235_ = l_Lean_addMacroScope(v_a_2232_, v___x_2234_, v_a_2230_);
v___x_2236_ = lean_box(0);
lean_inc_n(v___x_2228_, 4);
v___x_2237_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2228_);
lean_ctor_set(v___x_2237_, 1, v___x_2233_);
lean_ctor_set(v___x_2237_, 2, v___x_2235_);
lean_ctor_set(v___x_2237_, 3, v___x_2236_);
v___x_2238_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2228_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2241_ = l_Lean_Syntax_node1(v___x_2228_, v___x_2240_, v_stx_1739_);
v___x_2242_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2228_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = l_Lean_Syntax_node4(v___x_2228_, v___x_1751_, v___x_2237_, v___x_2239_, v___x_2241_, v___x_2243_);
v___x_2245_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2254_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2244_);
lean_ctor_set(v___x_2250_, 1, v_a_2246_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2250_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v___x_2244_);
v_a_2255_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2245_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2245_);
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
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v___x_2228_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2275_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2229_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2229_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2283_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2226_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2226_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2292_; 
lean_dec(v_id_1738_);
v_val_2291_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2292_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2291_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v_pat_1744_ = v_a_2293_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_stx_1739_);
v_a_2294_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2292_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
else
{
v___y_2093_ = v_a_1740_;
v___y_2094_ = v_a_1741_;
goto v___jp_2092_;
}
}
}
else
{
lean_dec(v___x_2145_);
v___y_2093_ = v_a_1740_;
v___y_2094_ = v_a_1741_;
goto v___jp_2092_;
}
v___jp_2066_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2072_ = lean_string_append(v___y_2070_, v___x_2071_);
lean_inc(v___y_2068_);
v___x_2073_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2068_, v_stx_2065_, v_id_1738_, v___x_2072_, v___y_2067_, v___y_2069_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v_pat_1744_ = v_a_2074_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_stx_1739_);
v_a_2075_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2073_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2073_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
v___jp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2087_ = l_Lean_Syntax_isStrLit_x3f(v___x_1985_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2089_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2088_);
v___y_2067_ = v___y_2084_;
v___y_2068_ = v___x_2086_;
v___y_2069_ = v___y_2085_;
v___y_2070_ = v___x_2089_;
goto v___jp_2066_;
}
else
{
lean_object* v_val_2090_; 
v_val_2090_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2087_, 1);
v___y_2067_ = v___y_2084_;
v___y_2068_ = v___x_2086_;
v___y_2069_ = v___y_2085_;
v___y_2070_ = v_val_2090_;
goto v___jp_2066_;
}
}
v___jp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(5u);
v___x_2096_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2095_);
v___x_2097_ = l_Lean_Syntax_isNone(v___x_2096_);
if (v___x_2097_ == 0)
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Lean_Syntax_matchesNull(v___x_2096_, v___x_2091_);
if (v___x_2098_ == 0)
{
lean_dec(v_stx_2065_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Elab_Command_getRef___redArg(v___y_2093_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = l_Lean_SourceInfo_fromRef(v_a_2100_, v___x_2098_);
lean_dec(v_a_2100_);
v___x_2102_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2093_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_quotContext_x3f_2103_; 
v_quotContext_x3f_2103_ = lean_ctor_get(v___y_2093_, 5);
if (lean_obj_tag(v_quotContext_x3f_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2105_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2094_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_1753_ = v___y_2094_;
v___y_1754_ = v___y_2093_;
v___y_1755_ = v_a_2104_;
v___y_1756_ = v___x_2101_;
v_a_1757_ = v_a_2106_;
goto v___jp_1752_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_a_2104_);
lean_dec(v___x_2101_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2107_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2105_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v_val_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2102_, 1);
v_val_2116_ = lean_ctor_get(v_quotContext_x3f_2103_, 0);
lean_inc(v_val_2116_);
v___y_1753_ = v___y_2094_;
v___y_1754_ = v___y_2093_;
v___y_1755_ = v_a_2115_;
v___y_1756_ = v___x_2101_;
v_a_1757_ = v_val_2116_;
goto v___jp_1752_;
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v___x_2101_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2117_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2102_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2102_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2125_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2099_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2099_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2134_; 
lean_dec(v_id_1738_);
v_val_2133_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2134_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2133_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_pat_1744_ = v_a_2135_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_stx_1739_);
v_a_2136_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2134_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2134_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1737_);
v___y_2084_ = v___y_2093_;
v___y_2085_ = v___y_2094_;
goto v___jp_2083_;
}
}
else
{
lean_dec(v___x_2096_);
lean_dec(v_id_x3f_1737_);
v___y_2084_ = v___y_2093_;
v___y_2085_ = v___y_2094_;
goto v___jp_2083_;
}
}
}
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2302_ = lean_unsigned_to_nat(1u);
v___x_2303_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2302_);
lean_inc(v___x_2303_);
v___x_2304_ = l_Lean_Syntax_matchesNull(v___x_2303_, v___x_2302_);
if (v___x_2304_ == 0)
{
lean_dec(v___x_2303_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = l_Lean_SourceInfo_fromRef(v_a_2306_, v___x_2304_);
lean_dec(v_a_2306_);
v___x_2308_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v_a_2311_; lean_object* v_quotContext_x3f_2342_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v_quotContext_x3f_2342_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2342_) == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_a_2311_ = v_a_2344_;
goto v___jp_2310_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2309_);
lean_dec(v___x_2307_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2345_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2343_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_val_2353_; 
v_val_2353_ = lean_ctor_get(v_quotContext_x3f_2342_, 0);
lean_inc(v_val_2353_);
v_a_2311_ = v_val_2353_;
goto v___jp_2310_;
}
v___jp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2312_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2313_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2314_ = l_Lean_addMacroScope(v_a_2311_, v___x_2313_, v_a_2309_);
v___x_2315_ = lean_box(0);
lean_inc_n(v___x_2307_, 4);
v___x_2316_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2307_);
lean_ctor_set(v___x_2316_, 1, v___x_2312_);
lean_ctor_set(v___x_2316_, 2, v___x_2314_);
lean_ctor_set(v___x_2316_, 3, v___x_2315_);
v___x_2317_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2307_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2320_ = l_Lean_Syntax_node1(v___x_2307_, v___x_2319_, v_stx_1739_);
v___x_2321_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2307_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_Syntax_node4(v___x_2307_, v___x_1751_, v___x_2316_, v___x_2318_, v___x_2320_, v___x_2322_);
v___x_2324_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2323_);
lean_ctor_set(v___x_2329_, 1, v_a_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v___x_2323_);
v_a_2334_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2324_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2324_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v___x_2307_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2354_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2308_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2308_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2362_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2305_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2305_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_val_2370_; lean_object* v___x_2371_; 
lean_dec(v_id_1738_);
v_val_2370_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2370_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2371_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2370_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v_pat_1744_ = v_a_2372_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_stx_1739_);
v_a_2373_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2371_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2381_ = lean_unsigned_to_nat(3u);
v___x_2382_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2381_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2382_);
v___x_2384_ = l_Lean_Syntax_isOfKind(v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_dec(v___x_2382_);
lean_dec(v___x_2303_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = l_Lean_SourceInfo_fromRef(v_a_2386_, v___x_1824_);
lean_dec(v_a_2386_);
v___x_2388_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v_a_2391_; lean_object* v_quotContext_x3f_2422_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v_quotContext_x3f_2422_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2422_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v_a_2391_ = v_a_2424_;
goto v___jp_2390_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_a_2389_);
lean_dec(v___x_2387_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2425_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2423_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2423_);
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
else
{
lean_object* v_val_2433_; 
v_val_2433_ = lean_ctor_get(v_quotContext_x3f_2422_, 0);
lean_inc(v_val_2433_);
v_a_2391_ = v_val_2433_;
goto v___jp_2390_;
}
v___jp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2392_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2394_ = l_Lean_addMacroScope(v_a_2391_, v___x_2393_, v_a_2389_);
v___x_2395_ = lean_box(0);
lean_inc_n(v___x_2387_, 4);
v___x_2396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2387_);
lean_ctor_set(v___x_2396_, 1, v___x_2392_);
lean_ctor_set(v___x_2396_, 2, v___x_2394_);
lean_ctor_set(v___x_2396_, 3, v___x_2395_);
v___x_2397_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2387_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2400_ = l_Lean_Syntax_node1(v___x_2387_, v___x_2399_, v_stx_1739_);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2387_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_Lean_Syntax_node4(v___x_2387_, v___x_1751_, v___x_2396_, v___x_2398_, v___x_2400_, v___x_2402_);
v___x_2404_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2413_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2403_);
lean_ctor_set(v___x_2409_, 1, v_a_2405_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2411_ = v___x_2407_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v___x_2403_);
v_a_2414_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2404_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2404_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v___x_2387_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2434_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2388_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2388_);
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
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2442_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2385_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2385_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_val_2450_; lean_object* v___x_2451_; 
lean_dec(v_id_1738_);
v_val_2450_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2451_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2450_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v_pat_1744_ = v_a_2452_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_stx_1739_);
v_a_2453_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2451_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2451_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
else
{
lean_object* v___x_2461_; lean_object* v_stx_2462_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2461_ = lean_unsigned_to_nat(0u);
v_stx_2462_ = l_Lean_Syntax_getArg(v___x_2303_, v___x_2461_);
lean_dec(v___x_2303_);
v___x_2488_ = lean_unsigned_to_nat(2u);
v___x_2541_ = lean_unsigned_to_nat(4u);
v___x_2542_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_isNone(v___x_2542_);
if (v___x_2543_ == 0)
{
uint8_t v___x_2544_; 
lean_inc(v___x_2542_);
v___x_2544_ = l_Lean_Syntax_matchesNull(v___x_2542_, v___x_2488_);
if (v___x_2544_ == 0)
{
lean_dec(v___x_2542_);
lean_dec(v_stx_2462_);
lean_dec(v___x_2382_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l_Lean_SourceInfo_fromRef(v_a_2546_, v___x_2544_);
lean_dec(v_a_2546_);
v___x_2548_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v_a_2551_; lean_object* v_quotContext_x3f_2582_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v_quotContext_x3f_2582_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2582_) == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v_a_2551_ = v_a_2584_;
goto v___jp_2550_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_a_2549_);
lean_dec(v___x_2547_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2585_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2583_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2583_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_val_2593_; 
v_val_2593_ = lean_ctor_get(v_quotContext_x3f_2582_, 0);
lean_inc(v_val_2593_);
v_a_2551_ = v_val_2593_;
goto v___jp_2550_;
}
v___jp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2553_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2554_ = l_Lean_addMacroScope(v_a_2551_, v___x_2553_, v_a_2549_);
v___x_2555_ = lean_box(0);
lean_inc_n(v___x_2547_, 4);
v___x_2556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2547_);
lean_ctor_set(v___x_2556_, 1, v___x_2552_);
lean_ctor_set(v___x_2556_, 2, v___x_2554_);
lean_ctor_set(v___x_2556_, 3, v___x_2555_);
v___x_2557_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2547_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2560_ = l_Lean_Syntax_node1(v___x_2547_, v___x_2559_, v_stx_1739_);
v___x_2561_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2547_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = l_Lean_Syntax_node4(v___x_2547_, v___x_1751_, v___x_2556_, v___x_2558_, v___x_2560_, v___x_2562_);
v___x_2564_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2573_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2563_);
lean_ctor_set(v___x_2569_, 1, v_a_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v___x_2563_);
v_a_2574_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2564_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2564_);
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
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v___x_2547_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2594_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2548_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2548_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2602_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2545_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2545_);
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
else
{
lean_object* v_val_2610_; lean_object* v___x_2611_; 
lean_dec(v_id_1738_);
v_val_2610_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2611_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2610_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_pat_1744_ = v_a_2612_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_stx_1739_);
v_a_2613_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2611_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2611_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = l_Lean_Syntax_getArg(v___x_2542_, v___x_2302_);
lean_dec(v___x_2542_);
v___x_2622_ = l_Lean_Syntax_matchesNull(v___x_2621_, v___x_2302_);
if (v___x_2622_ == 0)
{
lean_dec(v_stx_2462_);
lean_dec(v___x_2382_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = l_Lean_SourceInfo_fromRef(v_a_2624_, v___x_2622_);
lean_dec(v_a_2624_);
v___x_2626_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v_a_2629_; lean_object* v_quotContext_x3f_2660_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v_quotContext_x3f_2660_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2660_) == 0)
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v_a_2629_ = v_a_2662_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v_a_2627_);
lean_dec(v___x_2625_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2663_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2661_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_object* v_val_2671_; 
v_val_2671_ = lean_ctor_get(v_quotContext_x3f_2660_, 0);
lean_inc(v_val_2671_);
v_a_2629_ = v_val_2671_;
goto v___jp_2628_;
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2630_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2631_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2632_ = l_Lean_addMacroScope(v_a_2629_, v___x_2631_, v_a_2627_);
v___x_2633_ = lean_box(0);
lean_inc_n(v___x_2625_, 4);
v___x_2634_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2625_);
lean_ctor_set(v___x_2634_, 1, v___x_2630_);
lean_ctor_set(v___x_2634_, 2, v___x_2632_);
lean_ctor_set(v___x_2634_, 3, v___x_2633_);
v___x_2635_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2625_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2638_ = l_Lean_Syntax_node1(v___x_2625_, v___x_2637_, v_stx_1739_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2625_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = l_Lean_Syntax_node4(v___x_2625_, v___x_1751_, v___x_2634_, v___x_2636_, v___x_2638_, v___x_2640_);
v___x_2642_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2651_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2641_);
lean_ctor_set(v___x_2647_, 1, v_a_2643_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2647_);
v___x_2649_ = v___x_2645_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v___x_2641_);
v_a_2652_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2642_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2642_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v___x_2625_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2672_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2626_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2626_);
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
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2680_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2623_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2623_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2689_; 
lean_dec(v_id_1738_);
v_val_2688_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2689_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2688_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v_pat_1744_ = v_a_2690_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_stx_1739_);
v_a_2691_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2689_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
else
{
v___y_2490_ = v_a_1740_;
v___y_2491_ = v_a_1741_;
goto v___jp_2489_;
}
}
}
else
{
lean_dec(v___x_2542_);
v___y_2490_ = v_a_1740_;
v___y_2491_ = v_a_1741_;
goto v___jp_2489_;
}
v___jp_2463_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2469_ = lean_string_append(v___y_2467_, v___x_2468_);
lean_inc(v___y_2465_);
v___x_2470_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2465_, v_stx_2462_, v_id_1738_, v___x_2469_, v___y_2464_, v___y_2466_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v_pat_1744_ = v_a_2471_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_stx_1739_);
v_a_2472_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2470_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2470_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
v___jp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2484_ = l_Lean_Syntax_isStrLit_x3f(v___x_2382_);
lean_dec(v___x_2382_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2486_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2485_);
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___x_2483_;
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___x_2486_;
goto v___jp_2463_;
}
else
{
lean_object* v_val_2487_; 
v_val_2487_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v___x_2484_, 1);
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___x_2483_;
v___y_2466_ = v___y_2482_;
v___y_2467_ = v_val_2487_;
goto v___jp_2463_;
}
}
v___jp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2492_ = lean_unsigned_to_nat(5u);
v___x_2493_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2492_);
v___x_2494_ = l_Lean_Syntax_isNone(v___x_2493_);
if (v___x_2494_ == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = l_Lean_Syntax_matchesNull(v___x_2493_, v___x_2488_);
if (v___x_2495_ == 0)
{
lean_dec(v_stx_2462_);
lean_dec(v___x_2382_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_Elab_Command_getRef___redArg(v___y_2490_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v___x_2498_ = l_Lean_SourceInfo_fromRef(v_a_2497_, v___x_2495_);
lean_dec(v_a_2497_);
v___x_2499_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2490_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_quotContext_x3f_2500_; 
v_quotContext_x3f_2500_ = lean_ctor_get(v___y_2490_, 5);
if (lean_obj_tag(v_quotContext_x3f_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2502_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2491_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___y_1789_ = v_a_2501_;
v___y_1790_ = v___x_2498_;
v___y_1791_ = v___y_2491_;
v___y_1792_ = v___y_2490_;
v_a_1793_ = v_a_2503_;
goto v___jp_1788_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_a_2501_);
lean_dec(v___x_2498_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2504_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2502_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2502_);
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
lean_object* v_a_2512_; lean_object* v_val_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2499_, 1);
v_val_2513_ = lean_ctor_get(v_quotContext_x3f_2500_, 0);
lean_inc(v_val_2513_);
v___y_1789_ = v_a_2512_;
v___y_1790_ = v___x_2498_;
v___y_1791_ = v___y_2491_;
v___y_1792_ = v___y_2490_;
v_a_1793_ = v_val_2513_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v___x_2498_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2514_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2499_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2499_);
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
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2522_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2496_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2496_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_val_2530_; lean_object* v___x_2531_; 
lean_dec(v_id_1738_);
v_val_2530_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2531_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2530_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v_pat_1744_ = v_a_2532_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_stx_1739_);
v_a_2533_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2531_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2531_);
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
lean_dec(v_id_x3f_1737_);
v___y_2481_ = v___y_2490_;
v___y_2482_ = v___y_2491_;
goto v___jp_2480_;
}
}
else
{
lean_dec(v___x_2493_);
lean_dec(v_id_x3f_1737_);
v___y_2481_ = v___y_2490_;
v___y_2482_ = v___y_2491_;
goto v___jp_2480_;
}
}
}
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2699_);
v___x_2701_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2702_ = l_Lean_Syntax_matchesIdent(v___x_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2704_ = l_Lean_Syntax_matchesIdent(v___x_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2706_ = l_Lean_Syntax_matchesIdent(v___x_2700_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2708_ = l_Lean_Syntax_matchesIdent(v___x_2700_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2710_ = l_Lean_Syntax_matchesIdent(v___x_2700_, v___x_2709_);
lean_dec(v___x_2700_);
if (v___x_2710_ == 0)
{
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = l_Lean_SourceInfo_fromRef(v_a_2712_, v___x_2710_);
lean_dec(v_a_2712_);
v___x_2714_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v_a_2717_; lean_object* v_quotContext_x3f_2748_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v_quotContext_x3f_2748_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2748_) == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v_a_2717_ = v_a_2750_;
goto v___jp_2716_;
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2715_);
lean_dec(v___x_2713_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
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
else
{
lean_object* v_val_2759_; 
v_val_2759_ = lean_ctor_get(v_quotContext_x3f_2748_, 0);
lean_inc(v_val_2759_);
v_a_2717_ = v_val_2759_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2718_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2720_ = l_Lean_addMacroScope(v_a_2717_, v___x_2719_, v_a_2715_);
v___x_2721_ = lean_box(0);
lean_inc_n(v___x_2713_, 4);
v___x_2722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2713_);
lean_ctor_set(v___x_2722_, 1, v___x_2718_);
lean_ctor_set(v___x_2722_, 2, v___x_2720_);
lean_ctor_set(v___x_2722_, 3, v___x_2721_);
v___x_2723_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2713_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2726_ = l_Lean_Syntax_node1(v___x_2713_, v___x_2725_, v_stx_1739_);
v___x_2727_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2713_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = l_Lean_Syntax_node4(v___x_2713_, v___x_1751_, v___x_2722_, v___x_2724_, v___x_2726_, v___x_2728_);
v___x_2730_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2739_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2729_);
lean_ctor_set(v___x_2735_, 1, v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v___x_2729_);
v_a_2740_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2730_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2730_);
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
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v___x_2713_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2760_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2714_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2714_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2768_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2711_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2711_);
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
lean_object* v_val_2776_; lean_object* v___x_2777_; 
lean_dec(v_id_1738_);
v_val_2776_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2777_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2776_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v_pat_1744_ = v_a_2778_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_stx_1739_);
v_a_2779_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2777_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2777_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2787_ = lean_unsigned_to_nat(1u);
v___x_2788_ = lean_unsigned_to_nat(2u);
v___x_2789_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2788_);
lean_inc(v___x_2789_);
v___x_2790_ = l_Lean_Syntax_matchesNull(v___x_2789_, v___x_2787_);
if (v___x_2790_ == 0)
{
lean_dec(v___x_2789_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_SourceInfo_fromRef(v_a_2792_, v___x_2790_);
lean_dec(v_a_2792_);
v___x_2794_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v_a_2797_; lean_object* v_quotContext_x3f_2828_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v_quotContext_x3f_2828_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2828_) == 0)
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
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
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
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
lean_inc(v_stx_1739_);
v___x_2806_ = l_Lean_Syntax_node1(v___x_2793_, v___x_2805_, v_stx_1739_);
v___x_2807_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2793_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_Syntax_node4(v___x_2793_, v___x_1751_, v___x_2802_, v___x_2804_, v___x_2806_, v___x_2808_);
v___x_2810_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
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
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
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
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
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
lean_dec(v_id_1738_);
v_val_2856_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_2856_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_2857_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_2856_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_pat_1744_ = v_a_2858_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_stx_1739_);
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
lean_object* v_stx_2867_; lean_object* v___x_2868_; 
lean_dec(v_stx_1739_);
v_stx_2867_ = l_Lean_Syntax_getArg(v___x_2789_, v___x_2699_);
lean_dec(v___x_2789_);
v___x_2868_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1737_, v_id_1738_, v_stx_2867_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2931_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v_fst_2870_ = lean_ctor_get(v_a_2869_, 0);
v_snd_2871_ = lean_ctor_get(v_a_2869_, 1);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2873_ = v_a_2869_;
v_isShared_2874_ = v_isSharedCheck_2931_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_snd_2871_);
lean_inc(v_fst_2870_);
lean_dec(v_a_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2931_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = l_Lean_SourceInfo_fromRef(v_a_2876_, v___x_2708_);
lean_dec(v_a_2876_);
v___x_2878_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2914_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2914_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2914_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_a_2884_; lean_object* v_quotContext_x3f_2902_; 
v_quotContext_x3f_2902_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2902_) == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v_a_2884_ = v_a_2904_;
goto v___jp_2883_;
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_del_object(v___x_2881_);
lean_dec(v_a_2879_);
lean_dec(v___x_2877_);
lean_del_object(v___x_2873_);
lean_dec(v_snd_2871_);
lean_dec(v_fst_2870_);
v_a_2905_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2903_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2903_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_val_2913_; 
v_val_2913_ = lean_ctor_get(v_quotContext_x3f_2902_, 0);
lean_inc(v_val_2913_);
v_a_2884_ = v_val_2913_;
goto v___jp_2883_;
}
v___jp_2883_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2885_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_2886_ = l_Lean_addMacroScope(v_a_2884_, v___x_2709_, v_a_2879_);
v___x_2887_ = lean_box(0);
lean_inc_n(v___x_2877_, 4);
v___x_2888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2877_);
lean_ctor_set(v___x_2888_, 1, v___x_2885_);
lean_ctor_set(v___x_2888_, 2, v___x_2886_);
lean_ctor_set(v___x_2888_, 3, v___x_2887_);
v___x_2889_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2877_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_2892_ = l_Lean_Syntax_node1(v___x_2877_, v___x_2891_, v_fst_2870_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2877_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = l_Lean_Syntax_node4(v___x_2877_, v___x_1751_, v___x_2888_, v___x_2890_, v___x_2892_, v___x_2894_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2895_);
v___x_2897_ = v___x_2873_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_snd_2871_);
v___x_2897_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2899_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2897_);
v___x_2899_ = v___x_2881_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v___x_2877_);
lean_del_object(v___x_2873_);
lean_dec(v_snd_2871_);
lean_dec(v_fst_2870_);
v_a_2915_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2878_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2878_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_del_object(v___x_2873_);
lean_dec(v_snd_2871_);
lean_dec(v_fst_2870_);
v_a_2923_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2875_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2875_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
else
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
lean_dec(v___x_2700_);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_unsigned_to_nat(2u);
v___x_2934_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_2933_);
lean_inc(v___x_2934_);
v___x_2935_ = l_Lean_Syntax_matchesNull(v___x_2934_, v___x_2932_);
if (v___x_2935_ == 0)
{
lean_dec(v___x_2934_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l_Lean_SourceInfo_fromRef(v_a_2937_, v___x_2935_);
lean_dec(v_a_2937_);
v___x_2939_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v_a_2942_; lean_object* v_quotContext_x3f_2973_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v_quotContext_x3f_2973_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_2973_) == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v_a_2942_ = v_a_2975_;
goto v___jp_2941_;
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_a_2940_);
lean_dec(v___x_2938_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2976_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2974_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_val_2984_; 
v_val_2984_ = lean_ctor_get(v_quotContext_x3f_2973_, 0);
lean_inc(v_val_2984_);
v_a_2942_ = v_val_2984_;
goto v___jp_2941_;
}
v___jp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2943_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2944_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2945_ = l_Lean_addMacroScope(v_a_2942_, v___x_2944_, v_a_2940_);
v___x_2946_ = lean_box(0);
lean_inc_n(v___x_2938_, 4);
v___x_2947_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2938_);
lean_ctor_set(v___x_2947_, 1, v___x_2943_);
lean_ctor_set(v___x_2947_, 2, v___x_2945_);
lean_ctor_set(v___x_2947_, 3, v___x_2946_);
v___x_2948_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2938_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_2951_ = l_Lean_Syntax_node1(v___x_2938_, v___x_2950_, v_stx_1739_);
v___x_2952_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2938_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_Syntax_node4(v___x_2938_, v___x_1751_, v___x_2947_, v___x_2949_, v___x_2951_, v___x_2953_);
v___x_2955_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2964_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2954_);
lean_ctor_set(v___x_2960_, 1, v_a_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v___x_2954_);
v_a_2965_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2955_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2955_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v___x_2938_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2985_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2939_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2939_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_2993_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2936_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2936_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v_val_3001_; lean_object* v___x_3002_; 
lean_dec(v_id_1738_);
v_val_3001_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3001_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3002_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3001_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v_pat_1744_ = v_a_3003_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec(v_stx_1739_);
v_a_3004_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_3002_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_3002_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = l_Lean_Syntax_getArg(v___x_2934_, v___x_2699_);
lean_dec(v___x_2934_);
v___x_3013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3012_);
v___x_3014_ = l_Lean_Syntax_isOfKind(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec(v___x_3012_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = l_Lean_SourceInfo_fromRef(v_a_3016_, v___x_3014_);
lean_dec(v_a_3016_);
v___x_3018_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v_a_3021_; lean_object* v_quotContext_x3f_3052_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v_quotContext_x3f_3052_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3052_) == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v_a_3021_ = v_a_3054_;
goto v___jp_3020_;
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_3019_);
lean_dec(v___x_3017_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3055_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3053_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_val_3063_; 
v_val_3063_ = lean_ctor_get(v_quotContext_x3f_3052_, 0);
lean_inc(v_val_3063_);
v_a_3021_ = v_val_3063_;
goto v___jp_3020_;
}
v___jp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3022_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3024_ = l_Lean_addMacroScope(v_a_3021_, v___x_3023_, v_a_3019_);
v___x_3025_ = lean_box(0);
lean_inc_n(v___x_3017_, 4);
v___x_3026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3017_);
lean_ctor_set(v___x_3026_, 1, v___x_3022_);
lean_ctor_set(v___x_3026_, 2, v___x_3024_);
lean_ctor_set(v___x_3026_, 3, v___x_3025_);
v___x_3027_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3017_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3030_ = l_Lean_Syntax_node1(v___x_3017_, v___x_3029_, v_stx_1739_);
v___x_3031_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3017_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Lean_Syntax_node4(v___x_3017_, v___x_1751_, v___x_3026_, v___x_3028_, v___x_3030_, v___x_3032_);
v___x_3034_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3043_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3033_);
lean_ctor_set(v___x_3039_, 1, v_a_3035_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3039_);
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v___x_3033_);
v_a_3044_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3034_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3034_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v___x_3017_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3064_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3018_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3018_);
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
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3072_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3015_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3015_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_val_3080_; lean_object* v___x_3081_; 
lean_dec(v_id_1738_);
v_val_3080_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3080_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3081_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3080_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v_pat_1744_ = v_a_3082_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_stx_1739_);
v_a_3083_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3081_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3081_);
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
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = l_Lean_Syntax_getArg(v___x_3012_, v___x_2699_);
v___x_3092_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3093_ = l_Lean_Syntax_matchesIdent(v___x_3091_, v___x_3092_);
lean_dec(v___x_3091_);
if (v___x_3093_ == 0)
{
lean_dec(v___x_3012_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3096_ = l_Lean_SourceInfo_fromRef(v_a_3095_, v___x_3093_);
lean_dec(v_a_3095_);
v___x_3097_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v_a_3100_; lean_object* v_quotContext_x3f_3131_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_quotContext_x3f_3131_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3131_) == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v_a_3100_ = v_a_3133_;
goto v___jp_3099_;
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v_a_3098_);
lean_dec(v___x_3096_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3134_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3132_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3132_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_val_3142_; 
v_val_3142_ = lean_ctor_get(v_quotContext_x3f_3131_, 0);
lean_inc(v_val_3142_);
v_a_3100_ = v_val_3142_;
goto v___jp_3099_;
}
v___jp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3101_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3103_ = l_Lean_addMacroScope(v_a_3100_, v___x_3102_, v_a_3098_);
v___x_3104_ = lean_box(0);
lean_inc_n(v___x_3096_, 4);
v___x_3105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3096_);
lean_ctor_set(v___x_3105_, 1, v___x_3101_);
lean_ctor_set(v___x_3105_, 2, v___x_3103_);
lean_ctor_set(v___x_3105_, 3, v___x_3104_);
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3096_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3109_ = l_Lean_Syntax_node1(v___x_3096_, v___x_3108_, v_stx_1739_);
v___x_3110_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3096_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_Syntax_node4(v___x_3096_, v___x_1751_, v___x_3105_, v___x_3107_, v___x_3109_, v___x_3111_);
v___x_3113_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3122_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3112_);
lean_ctor_set(v___x_3118_, 1, v_a_3114_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3118_);
v___x_3120_ = v___x_3116_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v___x_3112_);
v_a_3123_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3113_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3113_);
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
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v___x_3096_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3143_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3097_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3097_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3151_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3094_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3094_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
lean_object* v_val_3159_; lean_object* v___x_3160_; 
lean_dec(v_id_1738_);
v_val_3159_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3160_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3159_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v_pat_1744_ = v_a_3161_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_stx_1739_);
v_a_3162_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3160_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3160_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
else
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = l_Lean_Syntax_getArg(v___x_3012_, v___x_2932_);
lean_dec(v___x_3012_);
v___x_3171_ = l_Lean_Syntax_matchesNull(v___x_3170_, v___x_2699_);
if (v___x_3171_ == 0)
{
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3174_ = l_Lean_SourceInfo_fromRef(v_a_3173_, v___x_3171_);
lean_dec(v_a_3173_);
v___x_3175_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v_a_3178_; lean_object* v_quotContext_x3f_3209_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3175_, 1);
v_quotContext_x3f_3209_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3209_) == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_a_3178_ = v_a_3211_;
goto v___jp_3177_;
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_a_3176_);
lean_dec(v___x_3174_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3212_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3210_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3210_);
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
else
{
lean_object* v_val_3220_; 
v_val_3220_ = lean_ctor_get(v_quotContext_x3f_3209_, 0);
lean_inc(v_val_3220_);
v_a_3178_ = v_val_3220_;
goto v___jp_3177_;
}
v___jp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3179_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3181_ = l_Lean_addMacroScope(v_a_3178_, v___x_3180_, v_a_3176_);
v___x_3182_ = lean_box(0);
lean_inc_n(v___x_3174_, 4);
v___x_3183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3174_);
lean_ctor_set(v___x_3183_, 1, v___x_3179_);
lean_ctor_set(v___x_3183_, 2, v___x_3181_);
lean_ctor_set(v___x_3183_, 3, v___x_3182_);
v___x_3184_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3174_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3187_ = l_Lean_Syntax_node1(v___x_3174_, v___x_3186_, v_stx_1739_);
v___x_3188_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3174_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_Syntax_node4(v___x_3174_, v___x_1751_, v___x_3183_, v___x_3185_, v___x_3187_, v___x_3189_);
v___x_3191_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3200_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3200_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3200_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3190_);
lean_ctor_set(v___x_3196_, 1, v_a_3192_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3196_);
v___x_3198_ = v___x_3194_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v___x_3190_);
v_a_3201_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3191_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3191_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v___x_3174_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3221_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3175_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3175_);
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
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3229_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3172_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3172_);
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
else
{
lean_object* v_val_3237_; lean_object* v___x_3238_; 
lean_dec(v_id_1738_);
v_val_3237_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3238_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3237_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v_pat_1744_ = v_a_3239_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_stx_1739_);
v_a_3240_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3238_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3238_);
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
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
lean_dec(v_id_x3f_1737_);
v___x_3248_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3249_ = lean_box(0);
v___x_3250_ = l_Lean_Syntax_mkAntiquotNode(v___x_3248_, v_id_1738_, v___x_2699_, v___x_3249_, v___x_2706_);
v_pat_1744_ = v___x_3250_;
goto v___jp_1743_;
}
}
}
}
}
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
lean_dec(v___x_2700_);
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_unsigned_to_nat(2u);
v___x_3253_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_3252_);
lean_inc(v___x_3253_);
v___x_3254_ = l_Lean_Syntax_matchesNull(v___x_3253_, v___x_3251_);
if (v___x_3254_ == 0)
{
lean_dec(v___x_3253_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v___x_3257_ = l_Lean_SourceInfo_fromRef(v_a_3256_, v___x_3254_);
lean_dec(v_a_3256_);
v___x_3258_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v_a_3261_; lean_object* v_quotContext_x3f_3292_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v_quotContext_x3f_3292_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3292_) == 0)
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v_a_3261_ = v_a_3294_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_a_3259_);
lean_dec(v___x_3257_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3295_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3293_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_val_3303_; 
v_val_3303_ = lean_ctor_get(v_quotContext_x3f_3292_, 0);
lean_inc(v_val_3303_);
v_a_3261_ = v_val_3303_;
goto v___jp_3260_;
}
v___jp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3262_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3263_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3264_ = l_Lean_addMacroScope(v_a_3261_, v___x_3263_, v_a_3259_);
v___x_3265_ = lean_box(0);
lean_inc_n(v___x_3257_, 4);
v___x_3266_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3257_);
lean_ctor_set(v___x_3266_, 1, v___x_3262_);
lean_ctor_set(v___x_3266_, 2, v___x_3264_);
lean_ctor_set(v___x_3266_, 3, v___x_3265_);
v___x_3267_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3257_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3270_ = l_Lean_Syntax_node1(v___x_3257_, v___x_3269_, v_stx_1739_);
v___x_3271_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3257_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_Lean_Syntax_node4(v___x_3257_, v___x_1751_, v___x_3266_, v___x_3268_, v___x_3270_, v___x_3272_);
v___x_3274_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3283_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3273_);
lean_ctor_set(v___x_3279_, 1, v_a_3275_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v___x_3273_);
v_a_3284_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3274_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3274_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec(v___x_3257_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3304_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3258_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3258_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3312_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3255_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3255_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_val_3320_; lean_object* v___x_3321_; 
lean_dec(v_id_1738_);
v_val_3320_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3321_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3320_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v_pat_1744_ = v_a_3322_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_stx_1739_);
v_a_3323_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3321_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3321_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
else
{
lean_object* v_stx_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec(v_id_x3f_1737_);
v_stx_3331_ = l_Lean_Syntax_getArg(v___x_3253_, v___x_2699_);
lean_dec(v___x_3253_);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3333_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2703_, v_stx_3331_, v_id_1738_, v___x_3332_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v_pat_1744_ = v_a_3334_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_stx_1739_);
v_a_3335_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3333_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3333_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
lean_dec(v___x_2700_);
v___x_3343_ = lean_unsigned_to_nat(1u);
v___x_3344_ = lean_unsigned_to_nat(2u);
v___x_3345_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_3344_);
lean_inc(v___x_3345_);
v___x_3346_ = l_Lean_Syntax_matchesNull(v___x_3345_, v___x_3343_);
if (v___x_3346_ == 0)
{
lean_dec(v___x_3345_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = l_Lean_SourceInfo_fromRef(v_a_3348_, v___x_3346_);
lean_dec(v_a_3348_);
v___x_3350_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v_a_3353_; lean_object* v_quotContext_x3f_3384_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v_quotContext_x3f_3384_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3384_) == 0)
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v_a_3353_ = v_a_3386_;
goto v___jp_3352_;
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_a_3351_);
lean_dec(v___x_3349_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3387_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3385_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v_val_3395_; 
v_val_3395_ = lean_ctor_get(v_quotContext_x3f_3384_, 0);
lean_inc(v_val_3395_);
v_a_3353_ = v_val_3395_;
goto v___jp_3352_;
}
v___jp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3354_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3356_ = l_Lean_addMacroScope(v_a_3353_, v___x_3355_, v_a_3351_);
v___x_3357_ = lean_box(0);
lean_inc_n(v___x_3349_, 4);
v___x_3358_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3349_);
lean_ctor_set(v___x_3358_, 1, v___x_3354_);
lean_ctor_set(v___x_3358_, 2, v___x_3356_);
lean_ctor_set(v___x_3358_, 3, v___x_3357_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3349_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3362_ = l_Lean_Syntax_node1(v___x_3349_, v___x_3361_, v_stx_1739_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3349_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Lean_Syntax_node4(v___x_3349_, v___x_1751_, v___x_3358_, v___x_3360_, v___x_3362_, v___x_3364_);
v___x_3366_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3375_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3365_);
lean_ctor_set(v___x_3371_, 1, v_a_3367_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3371_);
v___x_3373_ = v___x_3369_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v___x_3365_);
v_a_3376_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3366_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3366_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v___x_3349_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3396_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3350_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3350_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3404_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3347_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3347_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3413_; 
lean_dec(v_id_1738_);
v_val_3412_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3412_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3413_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3412_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v_pat_1744_ = v_a_3414_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_stx_1739_);
v_a_3415_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
lean_object* v_stx_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec(v_id_x3f_1737_);
v_stx_3423_ = l_Lean_Syntax_getArg(v___x_3345_, v___x_2699_);
lean_dec(v___x_3345_);
v___x_3424_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3425_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2703_, v_stx_3423_, v_id_1738_, v___x_3424_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v_pat_1744_ = v_a_3426_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_stx_1739_);
v_a_3427_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; 
lean_dec(v___x_2700_);
v___x_3435_ = lean_unsigned_to_nat(1u);
v___x_3436_ = lean_unsigned_to_nat(2u);
v___x_3437_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_3436_);
lean_inc(v___x_3437_);
v___x_3438_ = l_Lean_Syntax_matchesNull(v___x_3437_, v___x_3435_);
if (v___x_3438_ == 0)
{
lean_dec(v___x_3437_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = l_Lean_SourceInfo_fromRef(v_a_3440_, v___x_3438_);
lean_dec(v_a_3440_);
v___x_3442_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v_a_3445_; lean_object* v_quotContext_x3f_3476_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v_quotContext_x3f_3476_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3476_) == 0)
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v_a_3445_ = v_a_3478_;
goto v___jp_3444_;
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec(v_a_3443_);
lean_dec(v___x_3441_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3479_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3477_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3477_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_val_3487_; 
v_val_3487_ = lean_ctor_get(v_quotContext_x3f_3476_, 0);
lean_inc(v_val_3487_);
v_a_3445_ = v_val_3487_;
goto v___jp_3444_;
}
v___jp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3446_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3447_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3448_ = l_Lean_addMacroScope(v_a_3445_, v___x_3447_, v_a_3443_);
v___x_3449_ = lean_box(0);
lean_inc_n(v___x_3441_, 4);
v___x_3450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3441_);
lean_ctor_set(v___x_3450_, 1, v___x_3446_);
lean_ctor_set(v___x_3450_, 2, v___x_3448_);
lean_ctor_set(v___x_3450_, 3, v___x_3449_);
v___x_3451_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3441_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3454_ = l_Lean_Syntax_node1(v___x_3441_, v___x_3453_, v_stx_1739_);
v___x_3455_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3441_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = l_Lean_Syntax_node4(v___x_3441_, v___x_1751_, v___x_3450_, v___x_3452_, v___x_3454_, v___x_3456_);
v___x_3458_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3467_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3457_);
lean_ctor_set(v___x_3463_, 1, v_a_3459_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec(v___x_3457_);
v_a_3468_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3458_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3458_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v___x_3441_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3488_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3442_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3442_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3496_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3439_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3439_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_val_3504_; lean_object* v___x_3505_; 
lean_dec(v_id_1738_);
v_val_3504_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3505_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3504_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v_pat_1744_ = v_a_3506_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec(v_stx_1739_);
v_a_3507_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3505_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3505_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
else
{
lean_object* v_stx_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec(v_id_x3f_1737_);
v_stx_3515_ = l_Lean_Syntax_getArg(v___x_3437_, v___x_2699_);
lean_dec(v___x_3437_);
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3517_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2701_, v_stx_3515_, v_id_1738_, v___x_3516_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v_pat_1744_ = v_a_3518_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v_stx_1739_);
v_a_3519_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3517_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3517_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
v___jp_1752_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1758_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1760_ = l_Lean_addMacroScope(v_a_1757_, v___x_1759_, v___y_1755_);
v___x_1761_ = lean_box(0);
lean_inc_n(v___y_1756_, 4);
v___x_1762_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1762_, 0, v___y_1756_);
lean_ctor_set(v___x_1762_, 1, v___x_1758_);
lean_ctor_set(v___x_1762_, 2, v___x_1760_);
lean_ctor_set(v___x_1762_, 3, v___x_1761_);
v___x_1763_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___y_1756_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_1766_ = l_Lean_Syntax_node1(v___y_1756_, v___x_1765_, v_stx_1739_);
v___x_1767_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___y_1756_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_Syntax_node4(v___y_1756_, v___x_1751_, v___x_1762_, v___x_1764_, v___x_1766_, v___x_1768_);
v___x_1770_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v___y_1754_, v___y_1753_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1769_);
lean_ctor_set(v___x_1775_, 1, v_a_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v___x_1769_);
v_a_1780_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1770_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1770_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
v___jp_1788_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1794_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1796_ = l_Lean_addMacroScope(v_a_1793_, v___x_1795_, v___y_1789_);
v___x_1797_ = lean_box(0);
lean_inc_n(v___y_1790_, 4);
v___x_1798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1798_, 0, v___y_1790_);
lean_ctor_set(v___x_1798_, 1, v___x_1794_);
lean_ctor_set(v___x_1798_, 2, v___x_1796_);
lean_ctor_set(v___x_1798_, 3, v___x_1797_);
v___x_1799_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___y_1790_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_1802_ = l_Lean_Syntax_node1(v___y_1790_, v___x_1801_, v_stx_1739_);
v___x_1803_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1790_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = l_Lean_Syntax_node4(v___y_1790_, v___x_1751_, v___x_1798_, v___x_1800_, v___x_1802_, v___x_1804_);
v___x_1806_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v___y_1792_, v___y_1791_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1805_);
lean_ctor_set(v___x_1811_, 1, v_a_1807_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v___x_1805_);
v_a_1816_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1806_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1806_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3527_ = lean_unsigned_to_nat(1u);
v___x_3528_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_3527_);
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3528_);
v___x_3530_ = l_Lean_Syntax_isOfKind(v___x_3528_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_dec(v___x_3528_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = l_Lean_SourceInfo_fromRef(v_a_3532_, v___x_1748_);
lean_dec(v_a_3532_);
v___x_3534_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v_a_3537_; lean_object* v_quotContext_x3f_3569_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v_quotContext_x3f_3569_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3569_) == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v_a_3537_ = v_a_3571_;
goto v___jp_3536_;
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_a_3535_);
lean_dec(v___x_3533_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3572_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3570_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3570_);
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
lean_object* v_val_3580_; 
v_val_3580_ = lean_ctor_get(v_quotContext_x3f_3569_, 0);
lean_inc(v_val_3580_);
v_a_3537_ = v_val_3580_;
goto v___jp_3536_;
}
v___jp_3536_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3539_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3540_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3541_ = l_Lean_addMacroScope(v_a_3537_, v___x_3540_, v_a_3535_);
v___x_3542_ = lean_box(0);
lean_inc_n(v___x_3533_, 4);
v___x_3543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3533_);
lean_ctor_set(v___x_3543_, 1, v___x_3539_);
lean_ctor_set(v___x_3543_, 2, v___x_3541_);
lean_ctor_set(v___x_3543_, 3, v___x_3542_);
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3533_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3547_ = l_Lean_Syntax_node1(v___x_3533_, v___x_3546_, v_stx_1739_);
v___x_3548_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3533_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_Syntax_node4(v___x_3533_, v___x_3538_, v___x_3543_, v___x_3545_, v___x_3547_, v___x_3549_);
v___x_3551_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3560_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3560_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3560_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3550_);
lean_ctor_set(v___x_3556_, 1, v_a_3552_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3556_);
v___x_3558_ = v___x_3554_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v___x_3550_);
v_a_3561_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3551_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3551_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v___x_3533_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3581_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3534_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3534_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3589_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3531_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3531_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
else
{
lean_object* v_val_3597_; lean_object* v___x_3598_; 
lean_dec(v_id_1738_);
v_val_3597_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3597_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3598_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3597_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v_pat_1744_ = v_a_3599_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_stx_1739_);
v_a_3600_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3598_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3598_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
lean_dec(v_id_x3f_1737_);
v___x_3608_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3608_, 0, v___x_3528_);
v___x_3609_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3608_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3611_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3612_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3613_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3614_ = lean_unsigned_to_nat(4u);
v___x_3615_ = lean_mk_empty_array_with_capacity(v___x_3614_);
v___x_3616_ = lean_array_push(v___x_3615_, v_a_3610_);
v___x_3617_ = lean_array_push(v___x_3616_, v___x_3612_);
v___x_3618_ = lean_array_push(v___x_3617_, v___x_3613_);
v___x_3619_ = lean_array_push(v___x_3618_, v_id_1738_);
v___x_3620_ = lean_box(2);
v___x_3621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___x_3611_);
lean_ctor_set(v___x_3621_, 2, v___x_3619_);
v_pat_1744_ = v___x_3621_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3622_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3609_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3609_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_3630_);
v___x_3632_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3631_);
v___x_3633_ = l_Lean_Syntax_isOfKind(v___x_3631_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_dec(v___x_3631_);
if (lean_obj_tag(v_id_x3f_1737_) == 0)
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_Elab_Command_getRef___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
v___x_3636_ = l_Lean_SourceInfo_fromRef(v_a_3635_, v___x_3633_);
lean_dec(v_a_3635_);
v___x_3637_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1740_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_a_3640_; lean_object* v_quotContext_x3f_3672_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_quotContext_x3f_3672_ = lean_ctor_get(v_a_1740_, 5);
if (lean_obj_tag(v_quotContext_x3f_3672_) == 0)
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1741_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v_a_3640_ = v_a_3674_;
goto v___jp_3639_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_a_3638_);
lean_dec(v___x_3636_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
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
else
{
lean_object* v_val_3683_; 
v_val_3683_ = lean_ctor_get(v_quotContext_x3f_3672_, 0);
lean_inc(v_val_3683_);
v_a_3640_ = v_val_3683_;
goto v___jp_3639_;
}
v___jp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3642_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3643_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3644_ = l_Lean_addMacroScope(v_a_3640_, v___x_3643_, v_a_3638_);
v___x_3645_ = lean_box(0);
lean_inc_n(v___x_3636_, 4);
v___x_3646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3636_);
lean_ctor_set(v___x_3646_, 1, v___x_3642_);
lean_ctor_set(v___x_3646_, 2, v___x_3644_);
lean_ctor_set(v___x_3646_, 3, v___x_3645_);
v___x_3647_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3636_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1739_);
v___x_3650_ = l_Lean_Syntax_node1(v___x_3636_, v___x_3649_, v_stx_1739_);
v___x_3651_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3636_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = l_Lean_Syntax_node4(v___x_3636_, v___x_3641_, v___x_3646_, v___x_3648_, v___x_3650_, v___x_3652_);
v___x_3654_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_id_1738_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3663_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3653_);
lean_ctor_set(v___x_3659_, 1, v_a_3655_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v___x_3653_);
v_a_3664_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3654_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3654_);
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
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v___x_3636_);
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3684_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3637_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3637_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3692_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3634_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3634_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
else
{
lean_object* v_val_3700_; lean_object* v___x_3701_; 
lean_dec(v_id_1738_);
v_val_3700_ = lean_ctor_get(v_id_x3f_1737_, 0);
lean_inc(v_val_3700_);
lean_dec_ref_known(v_id_x3f_1737_, 1);
lean_inc(v_stx_1739_);
v___x_3701_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1739_, v_val_3700_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v_pat_1744_ = v_a_3702_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_stx_1739_);
v_a_3703_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3701_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3701_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec(v_id_x3f_1737_);
v___x_3711_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3711_, 0, v___x_3631_);
v___x_3712_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3711_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3715_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3716_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3717_ = lean_unsigned_to_nat(4u);
v___x_3718_ = lean_mk_empty_array_with_capacity(v___x_3717_);
v___x_3719_ = lean_array_push(v___x_3718_, v_a_3713_);
v___x_3720_ = lean_array_push(v___x_3719_, v___x_3715_);
v___x_3721_ = lean_array_push(v___x_3720_, v___x_3716_);
v___x_3722_ = lean_array_push(v___x_3721_, v_id_1738_);
v___x_3723_ = lean_box(2);
v___x_3724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v___x_3714_);
lean_ctor_set(v___x_3724_, 2, v___x_3722_);
v_pat_1744_ = v___x_3724_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_stx_1739_);
lean_dec(v_id_1738_);
v_a_3725_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3712_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3712_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_stx_1739_);
lean_ctor_set(v___x_1745_, 1, v_pat_1744_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3733_, lean_object* v_id_3734_, lean_object* v_stx_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3733_, v_id_3734_, v_stx_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3741_, v___y_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3745_, v_x_3746_, v___y_3747_, v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec_ref(v_x_3746_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3750_, lean_object* v_ref_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3751_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3756_, lean_object* v_ref_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3756_, v_ref_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3772_, lean_object* v_x_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3773_, v___y_3774_, v___y_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3778_, lean_object* v_x_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3778_, v_x_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3784_, lean_object* v_as_x27_3785_, lean_object* v_b_3786_, lean_object* v_a_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3785_, v_b_3786_, v___y_3788_, v___y_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3792_, lean_object* v_as_x27_3793_, lean_object* v_b_3794_, lean_object* v_a_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3792_, v_as_x27_3793_, v_b_3794_, v_a_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_as_x27_3793_);
lean_dec(v_as_3792_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3800_, lean_object* v_ref_3801_, lean_object* v_msg_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3801_, v_msg_3802_, v___y_3803_, v___y_3804_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3807_, lean_object* v_ref_3808_, lean_object* v_msg_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3807_, v_ref_3808_, v_msg_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v_ref_3808_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3814_, lean_object* v_m_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3815_, v_a_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3818_, lean_object* v_m_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3818_, v_m_3819_, v_a_3820_);
lean_dec(v_a_3820_);
lean_dec_ref(v_m_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3822_, lean_object* v_x_3823_, lean_object* v_x_3824_){
_start:
{
uint8_t v___x_3825_; 
v___x_3825_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3823_, v_x_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3826_, lean_object* v_x_3827_, lean_object* v_x_3828_){
_start:
{
uint8_t v_res_3829_; lean_object* v_r_3830_; 
v_res_3829_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_3826_, v_x_3827_, v_x_3828_);
lean_dec_ref(v_x_3828_);
lean_dec_ref(v_x_3827_);
v_r_3830_ = lean_box(v_res_3829_);
return v_r_3830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3831_, lean_object* v_a_3832_, lean_object* v_x_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_3832_, v_x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3835_, lean_object* v_a_3836_, lean_object* v_x_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_3835_, v_a_3836_, v_x_3837_);
lean_dec(v_x_3837_);
lean_dec(v_a_3836_);
return v_res_3838_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3839_, lean_object* v_x_3840_, size_t v_x_3841_, lean_object* v_x_3842_){
_start:
{
uint8_t v___x_3843_; 
v___x_3843_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_3840_, v_x_3841_, v_x_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3844_, lean_object* v_x_3845_, lean_object* v_x_3846_, lean_object* v_x_3847_){
_start:
{
size_t v_x_48306__boxed_3848_; uint8_t v_res_3849_; lean_object* v_r_3850_; 
v_x_48306__boxed_3848_ = lean_unbox_usize(v_x_3846_);
lean_dec(v_x_3846_);
v_res_3849_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_3844_, v_x_3845_, v_x_48306__boxed_3848_, v_x_3847_);
lean_dec_ref(v_x_3847_);
lean_dec_ref(v_x_3845_);
v_r_3850_ = lean_box(v_res_3849_);
return v_r_3850_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_3851_, lean_object* v_keys_3852_, lean_object* v_vals_3853_, lean_object* v_heq_3854_, lean_object* v_i_3855_, lean_object* v_k_3856_){
_start:
{
uint8_t v___x_3857_; 
v___x_3857_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_3852_, v_i_3855_, v_k_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3858_, lean_object* v_keys_3859_, lean_object* v_vals_3860_, lean_object* v_heq_3861_, lean_object* v_i_3862_, lean_object* v_k_3863_){
_start:
{
uint8_t v_res_3864_; lean_object* v_r_3865_; 
v_res_3864_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_3858_, v_keys_3859_, v_vals_3860_, v_heq_3861_, v_i_3862_, v_k_3863_);
lean_dec_ref(v_k_3863_);
lean_dec_ref(v_vals_3860_);
lean_dec_ref(v_keys_3859_);
v_r_3865_ = lean_box(v_res_3864_);
return v_r_3865_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_x_3872_){
_start:
{
lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3873_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_3874_ = lean_name_eq(v_x_3872_, v___x_3873_);
if (v___x_3874_ == 0)
{
uint8_t v___x_3875_; 
v___x_3875_ = 1;
return v___x_3875_;
}
else
{
uint8_t v___x_3876_; 
v___x_3876_ = 0;
return v___x_3876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_x_3877_){
_start:
{
uint8_t v_res_3878_; lean_object* v_r_3879_; 
v_res_3878_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_x_3877_);
lean_dec(v_x_3877_);
v_r_3879_ = lean_box(v_res_3878_);
return v_r_3879_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_3890_ = l_String_toRawSubstring_x27(v___x_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v___f_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___f_3897_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_3898_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMacrosReportingDeprecated___boxed), 9, 2);
lean_closure_set(v___x_3898_, 0, v_stx_3893_);
lean_closure_set(v___x_3898_, 1, v___f_3897_);
v___x_3899_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_3898_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc_n(v_a_3900_, 2);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_3902_ = l_Lean_Syntax_isOfKind(v_a_3900_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec(v_a_3900_);
v___x_3903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3912_ = lean_unsigned_to_nat(0u);
v___x_3913_ = l_Lean_Syntax_getArg(v_a_3900_, v___x_3912_);
v___x_3914_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3913_);
v___x_3915_ = l_Lean_Syntax_matchesNull(v___x_3913_, v___x_3914_);
if (v___x_3915_ == 0)
{
uint8_t v___x_3916_; 
v___x_3916_ = l_Lean_Syntax_matchesNull(v___x_3913_, v___x_3912_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_a_3900_);
v___x_3917_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = l_Lean_Syntax_getArg(v_a_3900_, v___x_3926_);
lean_dec(v_a_3900_);
v___x_3928_ = l_Lean_Elab_Command_getRef___redArg(v_a_3894_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = l_Lean_SourceInfo_fromRef(v_a_3929_, v___x_3915_);
lean_dec(v_a_3929_);
v___x_3931_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3894_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v_a_3934_; lean_object* v_quotContext_x3f_3942_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v_quotContext_x3f_3942_ = lean_ctor_get(v_a_3894_, 5);
if (lean_obj_tag(v_quotContext_x3f_3942_) == 0)
{
lean_object* v___x_3943_; lean_object* v_a_3944_; 
v___x_3943_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_3895_);
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3943_);
v_a_3934_ = v_a_3944_;
goto v___jp_3933_;
}
else
{
lean_object* v_val_3945_; 
v_val_3945_ = lean_ctor_get(v_quotContext_x3f_3942_, 0);
lean_inc(v_val_3945_);
v_a_3934_ = v_val_3945_;
goto v___jp_3933_;
}
v___jp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3935_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_3936_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_3937_ = l_Lean_addMacroScope(v_a_3934_, v___x_3936_, v_a_3932_);
v___x_3938_ = lean_box(0);
v___x_3939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3930_);
lean_ctor_set(v___x_3939_, 1, v___x_3935_);
lean_ctor_set(v___x_3939_, 2, v___x_3937_);
lean_ctor_set(v___x_3939_, 3, v___x_3938_);
v___x_3940_ = lean_box(0);
v___x_3941_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3940_, v___x_3939_, v___x_3927_, v_a_3894_, v_a_3895_);
return v___x_3941_;
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v___x_3930_);
lean_dec(v___x_3927_);
v_a_3946_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3931_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3931_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v___x_3927_);
v_a_3954_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3928_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3928_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3962_ = l_Lean_Syntax_getArg(v___x_3913_, v___x_3912_);
lean_dec(v___x_3913_);
v___x_3963_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_3962_);
v___x_3964_ = l_Lean_Syntax_isOfKind(v___x_3962_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v___x_3962_);
lean_dec(v_a_3900_);
v___x_3965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3974_ = lean_unsigned_to_nat(1u);
v___x_3975_ = l_Lean_Syntax_getArg(v_a_3900_, v___x_3974_);
lean_dec(v_a_3900_);
lean_inc(v___x_3962_);
v___x_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3962_);
v___x_3977_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3976_, v___x_3962_, v___x_3975_, v_a_3894_, v_a_3895_);
return v___x_3977_;
}
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
v_a_3978_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3899_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3899_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Elab_Command_expandMacroArg(v_stx_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
return v_res_3990_;
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
