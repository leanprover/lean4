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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_14929__boxed_65_; uint8_t v___x_14930__boxed_66_; lean_object* v_res_67_; 
v___x_14929__boxed_65_ = lean_unbox(v___x_59_);
v___x_14930__boxed_66_ = lean_unbox(v___x_60_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_57_, v___x_58_, v___x_14929__boxed_65_, v___x_14930__boxed_66_, v_x_61_, v___y_62_, v___y_63_);
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
uint8_t v___x_15057__boxed_172_; size_t v_i_boxed_173_; size_t v_stop_boxed_174_; lean_object* v_res_175_; 
v___x_15057__boxed_172_ = lean_unbox(v___x_164_);
v_i_boxed_173_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_stop_boxed_174_ = lean_unbox_usize(v_stop_167_);
lean_dec(v_stop_167_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_15057__boxed_172_, v_as_165_, v_i_boxed_173_, v_stop_boxed_174_, v_b_168_, v___y_169_, v___y_170_);
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
uint8_t v___x_15243__boxed_258_; size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v___x_15243__boxed_258_ = lean_unbox(v___x_250_);
v_i_boxed_259_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_253_);
lean_dec(v_stop_253_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_15243__boxed_258_, v_as_251_, v_i_boxed_259_, v_stop_boxed_260_, v_b_254_, v___y_255_, v___y_256_);
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
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
lean_ctor_set(v___x_355_, 4, v___x_353_);
lean_ctor_set(v___x_355_, 5, v___x_353_);
lean_ctor_set(v___x_355_, 6, v___x_353_);
lean_ctor_set(v___x_355_, 7, v___x_353_);
lean_ctor_set(v___x_355_, 8, v___x_353_);
lean_ctor_set(v___x_355_, 9, v___x_353_);
lean_ctor_set(v___x_355_, 10, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_unsigned_to_nat(32u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_359_ = ((size_t)5ULL);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_unsigned_to_nat(32u);
v___x_362_ = lean_mk_empty_array_with_capacity(v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__3);
v___x_364_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_360_);
lean_ctor_set(v___x_364_, 3, v___x_360_);
lean_ctor_set_usize(v___x_364_, 4, v___x_359_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_box(1);
v___x_366_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__4);
v___x_367_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__1);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
lean_ctor_set(v___x_368_, 2, v___x_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(lean_object* v_msgData_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_env_373_; uint8_t v___x_374_; lean_object* v_env_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_scopes_378_; lean_object* v___x_379_; lean_object* v_opts_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_372_ = lean_st_ref_get(v___y_370_);
v_env_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_env_373_);
lean_dec(v___x_372_);
v___x_374_ = 0;
v_env_375_ = l_Lean_Environment_setRecordingDeps(v_env_373_, v___x_374_);
v___x_376_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_377_ = lean_st_ref_get(v___y_370_);
v_scopes_378_ = lean_ctor_get(v___x_377_, 2);
lean_inc(v_scopes_378_);
lean_dec(v___x_377_);
v___x_379_ = l_List_head_x21___redArg(v___x_376_, v_scopes_378_);
lean_dec(v_scopes_378_);
v_opts_380_ = lean_ctor_get(v___x_379_, 1);
lean_inc_ref(v_opts_380_);
lean_dec(v___x_379_);
v___x_381_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__2);
v___x_382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___closed__5);
v___x_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_383_, 0, v_env_375_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_ctor_set(v___x_383_, 3, v_opts_380_);
v___x_384_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_msgData_369_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_386_, v___y_387_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Elab_Command_getRef___redArg(v___y_391_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v_macroStack_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v_macroStack_396_ = lean_ctor_get(v___y_391_, 4);
v___x_397_ = l_Lean_Elab_getBetterRef(v_a_395_, v_macroStack_396_);
lean_dec(v_a_395_);
v___x_398_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_390_, v___y_392_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___x_398_);
lean_inc(v_macroStack_396_);
v___x_400_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_a_399_, v_macroStack_396_, v___y_392_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_397_);
lean_ctor_set(v___x_405_, 1, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_msg_390_);
v_a_410_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_394_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_394_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg___boxed(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(uint8_t v___x_423_, lean_object* v_as_424_, size_t v_i_425_, size_t v_stop_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_a_432_; uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_425_, v_stop_426_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___y_442_; uint8_t v___x_453_; 
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
v___x_438_ = lean_array_uget_borrowed(v_as_424_, v_i_425_);
lean_inc(v___x_438_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_438_, v___x_437_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v___x_438_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_438_, v___x_454_);
if (v___x_455_ == 0)
{
goto v___jp_439_;
}
else
{
lean_object* v___x_456_; lean_object* v_id_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v_id_457_ = l_Lean_Syntax_getArg(v___x_438_, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_457_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_id_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v_id_457_);
goto v___jp_439_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_unsigned_to_nat(2u);
v___x_462_ = l_Lean_Syntax_getArg(v___x_438_, v___x_461_);
v___x_463_ = l_Lean_Syntax_matchesNull(v___x_462_, v___x_460_);
if (v___x_463_ == 0)
{
lean_dec(v_id_457_);
goto v___jp_439_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = l_Lean_TSyntax_getId(v_id_457_);
lean_dec(v_id_457_);
v___x_465_ = l_Lean_Parser_getParserAliasInfo(v___x_464_);
lean_dec(v___x_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v_stackSz_x3f_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v_stackSz_x3f_467_ = lean_ctor_get(v_a_466_, 1);
lean_inc(v_stackSz_x3f_467_);
lean_dec(v_a_466_);
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__7));
v___x_469_ = l_instBEqOption_beq___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__0(v_stackSz_x3f_467_, v___x_468_);
lean_dec(v_stackSz_x3f_467_);
if (v___x_469_ == 0)
{
goto v___jp_439_;
}
else
{
v_a_432_ = v_b_427_;
goto v___jp_431_;
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_b_427_);
v_a_470_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v___x_465_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_465_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_ref_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v_ref_474_ = lean_ctor_get(v___y_428_, 7);
v___x_475_ = lean_io_error_to_string(v_a_470_);
v___x_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = l_Lean_MessageData_ofFormat(v___x_476_);
lean_inc(v_ref_474_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_ref_474_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_478_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_483_; lean_object* v_id_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v_id_484_ = l_Lean_Syntax_getArg(v___x_438_, v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_484_);
v___x_486_ = l_Lean_Syntax_isOfKind(v_id_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v_id_484_);
goto v___jp_439_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = l_Lean_Syntax_getArg(v___x_438_, v___x_487_);
v___x_489_ = l_Lean_Syntax_isNone(v___x_488_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
lean_inc(v___x_488_);
v___x_490_ = l_Lean_Syntax_matchesNull(v___x_488_, v___x_487_);
if (v___x_490_ == 0)
{
lean_dec(v___x_488_);
lean_dec(v_id_484_);
goto v___jp_439_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = l_Lean_Syntax_getArg(v___x_488_, v___x_483_);
lean_dec(v___x_488_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_493_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec(v_id_484_);
goto v___jp_439_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(0);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_484_, v___x_483_, v___x_453_, v___x_423_, v___x_494_, v___y_428_, v___y_429_);
lean_dec(v_id_484_);
v___y_442_ = v___x_495_;
goto v___jp_441_;
}
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_488_);
v___x_496_ = lean_box(0);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___lam__0(v_id_484_, v___x_483_, v___x_453_, v___x_423_, v___x_496_, v___y_428_, v___y_429_);
lean_dec(v_id_484_);
v___y_442_ = v___x_497_;
goto v___jp_441_;
}
}
}
v___jp_439_:
{
lean_object* v___x_440_; 
lean_inc(v___x_438_);
v___x_440_ = lean_array_push(v_b_427_, v___x_438_);
v_a_432_ = v___x_440_;
goto v___jp_431_;
}
v___jp_441_:
{
if (lean_obj_tag(v___y_442_) == 0)
{
lean_object* v_a_443_; uint8_t v___x_444_; 
v_a_443_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___y_442_, 1);
v___x_444_ = lean_unbox(v_a_443_);
lean_dec(v_a_443_);
if (v___x_444_ == 0)
{
v_a_432_ = v_b_427_;
goto v___jp_431_;
}
else
{
goto v___jp_439_;
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v_b_427_);
v_a_445_ = lean_ctor_get(v___y_442_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___y_442_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___y_442_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___y_442_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
else
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_b_427_);
return v___x_498_;
}
v___jp_431_:
{
size_t v___x_433_; size_t v___x_434_; 
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_425_, v___x_433_);
v_i_425_ = v___x_434_;
v_b_427_ = v_a_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1___boxed(lean_object* v___x_499_, lean_object* v_as_500_, lean_object* v_i_501_, lean_object* v_stop_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_15725__boxed_507_; size_t v_i_boxed_508_; size_t v_stop_boxed_509_; lean_object* v_res_510_; 
v___x_15725__boxed_507_ = lean_unbox(v___x_499_);
v_i_boxed_508_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_stop_boxed_509_ = lean_unbox_usize(v_stop_502_);
lean_dec(v_stop_502_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_15725__boxed_507_, v_as_500_, v_i_boxed_508_, v_stop_boxed_509_, v_b_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_as_500_);
return v_res_510_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__8));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__10));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__0));
v___x_538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__1));
v___x_539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v_a_532_);
v___x_540_ = l_Lean_Syntax_isOfKind(v_a_532_, v___x_539_);
v___x_541_ = 1;
if (v___x_540_ == 0)
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_532_);
v___x_549_ = l_Lean_Syntax_isOfKind(v_a_532_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v_a_532_);
goto v___jp_542_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_a_555_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l_Lean_Syntax_getArg(v_a_532_, v___x_550_);
lean_dec(v_a_532_);
v___x_552_ = l_Lean_Syntax_getArgs(v___x_551_);
lean_dec(v___x_551_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_array_get_size(v___x_552_);
v___x_561_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_562_ = lean_nat_dec_lt(v___x_553_, v___x_560_);
if (v___x_562_ == 0)
{
lean_dec_ref(v___x_552_);
v_a_555_ = v___x_561_;
goto v___jp_554_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_560_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__1(v___x_540_, v___x_552_, v___x_563_, v___x_564_, v___x_561_, v_a_534_, v_a_535_);
lean_dec_ref(v___x_552_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v_a_555_ = v_a_566_;
goto v___jp_554_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_a_533_);
v_a_567_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_565_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_565_);
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
v___jp_554_:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_get_size(v_a_555_);
v___x_557_ = lean_nat_dec_eq(v___x_556_, v___x_550_);
if (v___x_557_ == 0)
{
lean_dec_ref(v_a_555_);
goto v___jp_542_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_array_fget(v_a_555_, v___x_553_);
lean_dec_ref(v_a_555_);
v_a_532_ = v___x_558_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___y_587_; lean_object* v___y_593_; lean_object* v_id_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v_id_603_ = l_Lean_Syntax_getArg(v_a_532_, v___x_575_);
v___x_604_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__0));
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v_id_603_);
v___x_606_ = l_Lean_Syntax_isOfKind(v_id_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
lean_dec(v_id_603_);
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
lean_inc(v_a_532_);
v___x_608_ = l_Lean_Syntax_isOfKind(v_a_532_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_a_532_);
goto v___jp_598_;
}
else
{
lean_object* v___x_609_; lean_object* v_a_611_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_616_ = l_Lean_Syntax_getArg(v_a_532_, v___x_609_);
lean_dec(v_a_532_);
v___x_617_ = l_Lean_Syntax_getArgs(v___x_616_);
lean_dec(v___x_616_);
v___x_618_ = lean_array_get_size(v___x_617_);
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_620_ = lean_nat_dec_lt(v___x_575_, v___x_618_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_617_);
v_a_611_ = v___x_619_;
goto v___jp_610_;
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
v___x_621_ = ((size_t)0ULL);
v___x_622_ = lean_usize_of_nat(v___x_618_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_606_, v___x_617_, v___x_621_, v___x_622_, v___x_619_, v_a_534_, v_a_535_);
lean_dec_ref(v___x_617_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_a_611_ = v_a_624_;
goto v___jp_610_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_533_);
v_a_625_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
v___jp_610_:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_get_size(v_a_611_);
v___x_613_ = lean_nat_dec_eq(v___x_612_, v___x_609_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_a_611_);
goto v___jp_598_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_array_fget(v_a_611_, v___x_575_);
lean_dec_ref(v_a_611_);
v_a_532_ = v___x_614_;
goto _start;
}
}
}
}
else
{
lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___x_715_; lean_object* v_a_717_; lean_object* v_a_723_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_728_ = l_Lean_Syntax_getArg(v_a_532_, v___x_715_);
v___x_729_ = l_Lean_Syntax_isNone(v___x_728_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; 
lean_inc(v___x_728_);
v___x_730_ = l_Lean_Syntax_matchesNull(v___x_728_, v___x_715_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
lean_dec(v_id_603_);
v___x_731_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_732_ = l_Lean_Syntax_isOfKind(v_a_532_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v___x_728_);
goto v___jp_581_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_733_ = l_Lean_Syntax_getArgs(v___x_728_);
lean_dec(v___x_728_);
v___x_734_ = lean_array_get_size(v___x_733_);
v___x_735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_736_ = lean_nat_dec_lt(v___x_575_, v___x_734_);
if (v___x_736_ == 0)
{
lean_dec_ref(v___x_733_);
v_a_723_ = v___x_735_;
goto v___jp_722_;
}
else
{
size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((size_t)0ULL);
v___x_738_ = lean_usize_of_nat(v___x_734_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__3(v___x_730_, v___x_733_, v___x_737_, v___x_738_, v___x_735_, v_a_534_, v_a_535_);
lean_dec_ref(v___x_733_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v_a_723_ = v_a_740_;
goto v___jp_722_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_533_);
v_a_741_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_739_);
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
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_749_ = l_Lean_Syntax_getArg(v___x_728_, v___x_575_);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__9));
v___x_751_ = l_Lean_Syntax_isOfKind(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
lean_dec(v_id_603_);
v___x_752_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__1));
v___x_753_ = l_Lean_Syntax_isOfKind(v_a_532_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v___x_728_);
goto v___jp_576_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = l_Lean_Syntax_getArgs(v___x_728_);
lean_dec(v___x_728_);
v___x_755_ = lean_array_get_size(v___x_754_);
v___x_756_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__2));
v___x_757_ = lean_nat_dec_lt(v___x_575_, v___x_755_);
if (v___x_757_ == 0)
{
lean_dec_ref(v___x_754_);
v_a_717_ = v___x_756_;
goto v___jp_716_;
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_755_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4(v___x_751_, v___x_754_, v___x_758_, v___x_759_, v___x_756_, v_a_534_, v_a_535_);
lean_dec_ref(v___x_754_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v_a_717_ = v_a_761_;
goto v___jp_716_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_533_);
v_a_762_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_760_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
else
{
lean_dec(v___x_728_);
lean_dec(v_a_532_);
v___y_634_ = v_a_534_;
v___y_635_ = v_a_535_;
goto v___jp_633_;
}
}
}
else
{
lean_dec(v___x_728_);
lean_dec(v_a_532_);
v___y_634_ = v_a_534_;
v___y_635_ = v_a_535_;
goto v___jp_633_;
}
v___jp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_inc(v_id_603_);
v___x_636_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserName_x3f___boxed), 8, 1);
lean_closure_set(v___x_636_, 0, v_id_603_);
v___x_637_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_636_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_706_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_706_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_706_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_706_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
if (lean_obj_tag(v_a_638_) == 1)
{
lean_object* v_val_642_; 
v_val_642_ = lean_ctor_get(v_a_638_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_a_638_, 1);
switch(lean_obj_tag(v_val_642_))
{
case 0:
{
lean_object* v_cat_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v_id_603_);
v_cat_643_ = lean_ctor_get(v_val_642_, 0);
lean_inc(v_cat_643_);
lean_dec_ref_known(v_val_642_, 1);
v___x_644_ = lean_box(0);
v___x_645_ = l_Lean_Syntax_mkAntiquotNode(v_cat_643_, v_a_533_, v___x_575_, v___x_644_, v___x_541_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_645_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
case 1:
{
lean_object* v_decl_649_; 
lean_del_object(v___x_640_);
lean_dec(v_id_603_);
v_decl_649_ = lean_ctor_get(v_val_642_, 0);
lean_inc(v_decl_649_);
lean_dec_ref_known(v_val_642_, 1);
if (lean_obj_tag(v_decl_649_) == 1)
{
lean_object* v_pre_650_; 
v_pre_650_ = lean_ctor_get(v_decl_649_, 0);
if (lean_obj_tag(v_pre_650_) == 1)
{
lean_object* v_pre_651_; 
v_pre_651_ = lean_ctor_get(v_pre_650_, 0);
if (lean_obj_tag(v_pre_651_) == 1)
{
lean_object* v_pre_652_; 
v_pre_652_ = lean_ctor_get(v_pre_651_, 0);
switch(lean_obj_tag(v_pre_652_))
{
case 0:
{
lean_object* v_str_653_; lean_object* v_str_654_; lean_object* v_str_655_; uint8_t v___x_656_; 
v_str_653_ = lean_ctor_get(v_decl_649_, 1);
v_str_654_ = lean_ctor_get(v_pre_650_, 1);
v_str_655_ = lean_ctor_get(v_pre_651_, 1);
v___x_656_ = lean_string_dec_eq(v_str_655_, v___x_537_);
if (v___x_656_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = lean_string_dec_eq(v_str_654_, v___x_538_);
if (v___x_657_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_string_dec_eq(v_str_653_, v___x_604_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__3));
v___x_660_ = lean_string_dec_eq(v_str_653_, v___x_659_);
if (v___x_660_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
lean_object* v___x_661_; 
lean_dec_ref_known(v_decl_649_, 2);
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
v___y_593_ = v___x_661_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_662_; 
lean_dec_ref_known(v_decl_649_, 2);
v___x_662_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_593_ = v___x_662_;
goto v___jp_592_;
}
}
}
}
case 1:
{
lean_object* v_pre_663_; 
v_pre_663_ = lean_ctor_get(v_pre_652_, 0);
if (lean_obj_tag(v_pre_663_) == 0)
{
lean_object* v_str_664_; lean_object* v_str_665_; lean_object* v_str_666_; lean_object* v_str_667_; uint8_t v___x_668_; 
v_str_664_ = lean_ctor_get(v_decl_649_, 1);
v_str_665_ = lean_ctor_get(v_pre_650_, 1);
v_str_666_ = lean_ctor_get(v_pre_651_, 1);
v_str_667_ = lean_ctor_get(v_pre_652_, 1);
v___x_668_ = lean_string_dec_eq(v_str_667_, v___x_537_);
if (v___x_668_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_string_dec_eq(v_str_666_, v___x_538_);
if (v___x_669_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__7));
v___x_671_ = lean_string_dec_eq(v_str_665_, v___x_670_);
if (v___x_671_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = lean_string_dec_eq(v_str_664_, v___x_604_);
if (v___x_672_ == 0)
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
else
{
lean_object* v___x_673_; 
lean_dec_ref_known(v_decl_649_, 2);
v___x_673_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__6);
v___y_593_ = v___x_673_;
goto v___jp_592_;
}
}
}
}
}
else
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
}
default: 
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
}
}
else
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
}
else
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
}
else
{
v___y_593_ = v_decl_649_;
goto v___jp_592_;
}
}
default: 
{
lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_698_; 
lean_del_object(v___x_640_);
v_isSharedCheck_698_ = !lean_is_exclusive(v_val_642_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_val_642_, 0);
lean_dec(v_unused_699_);
v___x_675_ = v_val_642_;
v_isShared_676_ = v_isSharedCheck_698_;
goto v_resetjp_674_;
}
else
{
lean_dec(v_val_642_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_698_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = l_Lean_TSyntax_getId(v_id_603_);
lean_dec(v_id_603_);
v___x_678_ = l_Lean_Name_eraseMacroScopes(v___x_677_);
lean_dec(v___x_677_);
v___x_679_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v___x_678_);
lean_dec(v___x_678_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; 
lean_del_object(v___x_675_);
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
if (lean_obj_tag(v_a_680_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_box(0);
v___y_587_ = v___x_681_;
goto v___jp_586_;
}
else
{
lean_object* v_val_682_; 
v_val_682_ = lean_ctor_get(v_a_680_, 0);
lean_inc(v_val_682_);
lean_dec_ref_known(v_a_680_, 1);
v___y_587_ = v_val_682_;
goto v___jp_586_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_a_533_);
v_a_683_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_697_ == 0)
{
v___x_685_ = v___x_679_;
v_isShared_686_ = v_isSharedCheck_697_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_679_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_697_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_ref_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_ref_687_ = lean_ctor_get(v___y_634_, 7);
v___x_688_ = lean_io_error_to_string(v_a_683_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 3);
lean_ctor_set(v___x_675_, 0, v___x_688_);
v___x_690_ = v___x_675_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_696_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_691_ = l_Lean_MessageData_ofFormat(v___x_690_);
lean_inc(v_ref_687_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_ref_687_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_692_);
v___x_694_ = v___x_685_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
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
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_del_object(v___x_640_);
lean_dec(v_a_638_);
lean_dec(v_a_533_);
v___x_700_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__9);
v___x_701_ = l_Lean_MessageData_ofSyntax(v_id_603_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__11);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v___x_704_, v___y_634_, v___y_635_);
return v___x_705_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_id_603_);
lean_dec(v_a_533_);
v_a_707_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_637_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_637_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_get_size(v_a_717_);
v___x_719_ = lean_nat_dec_eq(v___x_718_, v___x_715_);
if (v___x_719_ == 0)
{
lean_dec_ref(v_a_717_);
goto v___jp_576_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_array_fget(v_a_717_, v___x_575_);
lean_dec_ref(v_a_717_);
v_a_532_ = v___x_720_;
goto _start;
}
}
v___jp_722_:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_array_get_size(v_a_723_);
v___x_725_ = lean_nat_dec_eq(v___x_724_, v___x_715_);
if (v___x_725_ == 0)
{
lean_dec_ref(v_a_723_);
goto v___jp_581_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = lean_array_fget(v_a_723_, v___x_575_);
lean_dec_ref(v_a_723_);
v_a_532_ = v___x_726_;
goto _start;
}
}
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_box(0);
v___x_579_ = l_Lean_Syntax_mkAntiquotNode(v___x_577_, v_a_533_, v___x_575_, v___x_578_, v___x_541_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
v___jp_581_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(0);
v___x_583_ = lean_box(0);
v___x_584_ = l_Lean_Syntax_mkAntiquotNode(v___x_582_, v_a_533_, v___x_575_, v___x_583_, v___x_541_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
v___jp_586_:
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_box(0);
v___x_589_ = 0;
v___x_590_ = l_Lean_Syntax_mkAntiquotNode(v___y_587_, v_a_533_, v___x_575_, v___x_588_, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
v___jp_592_:
{
lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_box(0);
v___x_595_ = 0;
v___x_596_ = l_Lean_Syntax_mkAntiquotNode(v___y_593_, v_a_533_, v___x_575_, v___x_594_, v___x_595_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_box(0);
v___x_601_ = l_Lean_Syntax_mkAntiquotNode(v___x_599_, v_a_533_, v___x_575_, v___x_600_, v___x_541_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
v___jp_542_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_box(0);
v___x_546_ = l_Lean_Syntax_mkAntiquotNode(v___x_543_, v_a_533_, v___x_544_, v___x_545_, v___x_541_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___boxed(lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(lean_object* v_msgData_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msgData_776_, v___y_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___boxed(lean_object* v_msgData_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2(v_msgData_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(lean_object* v_00_u03b1_786_, lean_object* v_msg_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_787_, v___y_788_, v___y_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___boxed(lean_object* v_00_u03b1_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2(v_00_u03b1_792_, v_msg_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(lean_object* v_msgData_798_, lean_object* v_macroStack_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___redArg(v_msgData_798_, v_macroStack_799_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3___boxed(lean_object* v_msgData_804_, lean_object* v_macroStack_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__3(v_msgData_804_, v_macroStack_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(lean_object* v_kind_813_, lean_object* v_stx_814_, lean_object* v_id_815_, lean_object* v_suffix_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_814_, v_id_815_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_835_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_835_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_835_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_835_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_825_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(v_kind_813_, v_a_821_, v_suffix_816_);
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
v___x_828_ = lean_array_push(v___x_827_, v___x_825_);
v___x_829_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_830_ = lean_box(2);
v___x_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
lean_ctor_set(v___x_831_, 2, v___x_828_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_831_);
v___x_833_ = v___x_823_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_dec_ref(v_suffix_816_);
lean_dec(v_kind_813_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___boxed(lean_object* v_kind_836_, lean_object* v_stx_837_, lean_object* v_id_838_, lean_object* v_suffix_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v_kind_836_, v_stx_837_, v_id_838_, v_suffix_839_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_env_847_; lean_object* v___x_848_; lean_object* v_mainModule_849_; lean_object* v___x_850_; 
v___x_846_ = lean_st_ref_get(v___y_844_);
v_env_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc_ref(v_env_847_);
lean_dec(v___x_846_);
v___x_848_ = l_Lean_Environment_header(v_env_847_);
lean_dec_ref(v_env_847_);
v_mainModule_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_mainModule_849_);
lean_dec_ref(v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_mainModule_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg___boxed(lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_851_);
lean_dec(v___y_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___boxed(lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0(v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(lean_object* v_msg_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_865_ = lean_panic_fn_borrowed(v___x_864_, v_msg_863_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = l_Lean_maxRecDepthErrorMessage;
v___x_872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__3);
v___x_874_ = l_Lean_MessageData_ofFormat(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__4);
v___x_876_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__2));
v___x_877_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(lean_object* v_ref_878_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___closed__5);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_ref_878_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg___boxed(lean_object* v_ref_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_883_);
return v_res_885_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_886_, lean_object* v_i_887_, lean_object* v_k_888_){
_start:
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_get_size(v_keys_886_);
v___x_890_ = lean_nat_dec_lt(v_i_887_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec(v_i_887_);
return v___x_890_;
}
else
{
lean_object* v_k_x27_891_; uint8_t v___x_892_; 
v_k_x27_891_ = lean_array_fget_borrowed(v_keys_886_, v_i_887_);
v___x_892_ = l_Lean_instBEqExtraModUse_beq(v_k_888_, v_k_x27_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_i_887_, v___x_893_);
lean_dec(v_i_887_);
v_i_887_ = v___x_894_;
goto _start;
}
else
{
lean_dec(v_i_887_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_896_, lean_object* v_i_897_, lean_object* v_k_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_896_, v_i_897_, v_k_898_);
lean_dec_ref(v_k_898_);
lean_dec_ref(v_keys_896_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(lean_object* v_x_901_, size_t v_x_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_object* v_es_904_; lean_object* v___x_905_; size_t v___x_906_; size_t v___x_907_; lean_object* v_j_908_; lean_object* v___x_909_; 
v_es_904_ = lean_ctor_get(v_x_901_, 0);
v___x_905_ = lean_box(2);
v___x_906_ = ((size_t)31ULL);
v___x_907_ = lean_usize_land(v_x_902_, v___x_906_);
v_j_908_ = lean_usize_to_nat(v___x_907_);
v___x_909_ = lean_array_get_borrowed(v___x_905_, v_es_904_, v_j_908_);
lean_dec(v_j_908_);
switch(lean_obj_tag(v___x_909_))
{
case 0:
{
lean_object* v_key_910_; uint8_t v___x_911_; 
v_key_910_ = lean_ctor_get(v___x_909_, 0);
v___x_911_ = l_Lean_instBEqExtraModUse_beq(v_x_903_, v_key_910_);
return v___x_911_;
}
case 1:
{
lean_object* v_node_912_; size_t v___x_913_; size_t v___x_914_; 
v_node_912_ = lean_ctor_get(v___x_909_, 0);
v___x_913_ = ((size_t)5ULL);
v___x_914_ = lean_usize_shift_right(v_x_902_, v___x_913_);
v_x_901_ = v_node_912_;
v_x_902_ = v___x_914_;
goto _start;
}
default: 
{
uint8_t v___x_916_; 
v___x_916_ = 0;
return v___x_916_;
}
}
}
else
{
lean_object* v_ks_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_ks_917_ = lean_ctor_get(v_x_901_, 0);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_ks_917_, v___x_918_, v_x_903_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
size_t v_x_42667__boxed_923_; uint8_t v_res_924_; lean_object* v_r_925_; 
v_x_42667__boxed_923_ = lean_unbox_usize(v_x_921_);
lean_dec(v_x_921_);
v_res_924_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_920_, v_x_42667__boxed_923_, v_x_922_);
lean_dec_ref(v_x_922_);
lean_dec_ref(v_x_920_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
uint64_t v___x_928_; size_t v___x_929_; uint8_t v___x_930_; 
v___x_928_ = l_Lean_instHashableExtraModUse_hash(v_x_927_);
v___x_929_ = lean_uint64_to_usize(v___x_928_);
v___x_930_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_926_, v___x_929_, v_x_927_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_931_, v_x_932_);
lean_dec_ref(v_x_932_);
lean_dec_ref(v_x_931_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_935_; double v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_float_of_nat(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(lean_object* v_cls_939_, lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Elab_Command_getRef___redArg(v___y_941_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_995_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2_spec__2___redArg(v_msg_940_, v___y_942_);
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_995_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_995_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_995_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v_traceState_952_; lean_object* v_env_953_; lean_object* v_messages_954_; lean_object* v_scopes_955_; lean_object* v_usedQuotCtxts_956_; lean_object* v_nextMacroScope_957_; lean_object* v_maxRecDepth_958_; lean_object* v_ngen_959_; lean_object* v_auxDeclNGen_960_; lean_object* v_infoState_961_; lean_object* v_snapshotTasks_962_; lean_object* v_prevLinterStates_963_; lean_object* v_codeQualityEntryTasks_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_994_; 
v___x_951_ = lean_st_ref_take(v___y_942_);
v_traceState_952_ = lean_ctor_get(v___x_951_, 9);
v_env_953_ = lean_ctor_get(v___x_951_, 0);
v_messages_954_ = lean_ctor_get(v___x_951_, 1);
v_scopes_955_ = lean_ctor_get(v___x_951_, 2);
v_usedQuotCtxts_956_ = lean_ctor_get(v___x_951_, 3);
v_nextMacroScope_957_ = lean_ctor_get(v___x_951_, 4);
v_maxRecDepth_958_ = lean_ctor_get(v___x_951_, 5);
v_ngen_959_ = lean_ctor_get(v___x_951_, 6);
v_auxDeclNGen_960_ = lean_ctor_get(v___x_951_, 7);
v_infoState_961_ = lean_ctor_get(v___x_951_, 8);
v_snapshotTasks_962_ = lean_ctor_get(v___x_951_, 10);
v_prevLinterStates_963_ = lean_ctor_get(v___x_951_, 11);
v_codeQualityEntryTasks_964_ = lean_ctor_get(v___x_951_, 12);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_994_ == 0)
{
v___x_966_ = v___x_951_;
v_isShared_967_ = v_isSharedCheck_994_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_codeQualityEntryTasks_964_);
lean_inc(v_prevLinterStates_963_);
lean_inc(v_snapshotTasks_962_);
lean_inc(v_traceState_952_);
lean_inc(v_infoState_961_);
lean_inc(v_auxDeclNGen_960_);
lean_inc(v_ngen_959_);
lean_inc(v_maxRecDepth_958_);
lean_inc(v_nextMacroScope_957_);
lean_inc(v_usedQuotCtxts_956_);
lean_inc(v_scopes_955_);
lean_inc(v_messages_954_);
lean_inc(v_env_953_);
lean_dec(v___x_951_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_994_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint64_t v_tid_968_; lean_object* v_traces_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_993_; 
v_tid_968_ = lean_ctor_get_uint64(v_traceState_952_, sizeof(void*)*1);
v_traces_969_ = lean_ctor_get(v_traceState_952_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_traceState_952_);
if (v_isSharedCheck_993_ == 0)
{
v___x_971_ = v_traceState_952_;
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_traces_969_);
lean_dec(v_traceState_952_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; double v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_box(0);
v___x_975_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__0);
v___x_976_ = 0;
v___x_977_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_978_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_978_, 0, v_cls_939_);
lean_ctor_set(v___x_978_, 1, v___x_974_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
lean_ctor_set_float(v___x_978_, sizeof(void*)*3, v___x_975_);
lean_ctor_set_float(v___x_978_, sizeof(void*)*3 + 8, v___x_975_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*3 + 16, v___x_976_);
v___x_979_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___closed__1));
v___x_980_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v_a_947_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_a_945_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_PersistentArray_push___redArg(v_traces_969_, v___x_981_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_982_);
v___x_984_ = v___x_971_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_982_);
lean_ctor_set_uint64(v_reuseFailAlloc_992_, sizeof(void*)*1, v_tid_968_);
v___x_984_ = v_reuseFailAlloc_992_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 9, v___x_984_);
v___x_986_ = v___x_966_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_env_953_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_messages_954_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_scopes_955_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_usedQuotCtxts_956_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_nextMacroScope_957_);
lean_ctor_set(v_reuseFailAlloc_991_, 5, v_maxRecDepth_958_);
lean_ctor_set(v_reuseFailAlloc_991_, 6, v_ngen_959_);
lean_ctor_set(v_reuseFailAlloc_991_, 7, v_auxDeclNGen_960_);
lean_ctor_set(v_reuseFailAlloc_991_, 8, v_infoState_961_);
lean_ctor_set(v_reuseFailAlloc_991_, 9, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_991_, 10, v_snapshotTasks_962_);
lean_ctor_set(v_reuseFailAlloc_991_, 11, v_prevLinterStates_963_);
lean_ctor_set(v_reuseFailAlloc_991_, 12, v_codeQualityEntryTasks_964_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_st_ref_put(v___y_942_, v___x_986_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_973_);
v___x_989_ = v___x_949_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_973_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_msg_940_);
lean_dec(v_cls_939_);
v_a_996_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_944_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_944_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2___boxed(lean_object* v_cls_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1004_, v_msg_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0(lean_object* v___x_1010_, lean_object* v_entry_1011_, lean_object* v_s_1012_){
_start:
{
lean_object* v_addEntryFn_1013_; lean_object* v_importedEntries_1014_; lean_object* v_state_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_addEntryFn_1013_ = lean_ctor_get(v___x_1010_, 3);
lean_inc(v_addEntryFn_1013_);
lean_dec_ref(v___x_1010_);
v_importedEntries_1014_ = lean_ctor_get(v_s_1012_, 0);
v_state_1015_ = lean_ctor_get(v_s_1012_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_s_1012_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1017_ = v_s_1012_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_state_1015_);
lean_inc(v_importedEntries_1014_);
lean_dec(v_s_1012_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_state_1019_; lean_object* v___x_1021_; 
v_state_1019_ = lean_apply_2(v_addEntryFn_1013_, v_state_1015_, v_entry_1011_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v_state_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_importedEntries_1014_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_state_1019_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1024_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__3));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__5));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9(void){
_start:
{
lean_object* v_cls_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_cls_1037_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1038_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
v___x_1039_ = l_Lean_Name_append(v___x_1038_, v_cls_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__10));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__12));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(lean_object* v_mod_1050_, uint8_t v_isMeta_1051_, lean_object* v_hint_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_env_1077_; uint8_t v_isExporting_1078_; lean_object* v_entry_1079_; lean_object* v___x_1080_; lean_object* v_env_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1075_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__0);
v___x_1076_ = lean_st_ref_get(v___y_1054_);
v_env_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref(v_env_1077_);
lean_dec(v___x_1076_);
v_isExporting_1078_ = lean_ctor_get_uint8(v_env_1077_, sizeof(void*)*13);
lean_dec_ref(v_env_1077_);
lean_inc(v_mod_1050_);
v_entry_1079_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1079_, 0, v_mod_1050_);
lean_ctor_set_uint8(v_entry_1079_, sizeof(void*)*1, v_isExporting_1078_);
lean_ctor_set_uint8(v_entry_1079_, sizeof(void*)*1 + 1, v_isMeta_1051_);
v___x_1080_ = lean_st_ref_get(v___y_1054_);
v_env_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_ref(v_env_1081_);
lean_dec(v___x_1080_);
v___x_1082_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1083_ = lean_box(1);
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1075_, v___x_1082_, v_env_1081_, v___x_1083_, v___x_1084_);
v___x_1086_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v___x_1085_, v_entry_1079_);
lean_dec(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___f_1087_; uint8_t v___x_1088_; lean_object* v___y_1090_; lean_object* v_cls_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v_scopes_1137_; lean_object* v___x_1138_; lean_object* v_opts_1139_; uint8_t v_hasTrace_1140_; 
v___f_1087_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_1087_, 0, v___x_1082_);
lean_closure_set(v___f_1087_, 1, v_entry_1079_);
v___x_1088_ = 1;
v_cls_1112_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__2));
v___x_1113_ = l_Lean_inheritedTraceOptions;
v___x_1114_ = lean_st_ref_get(v___x_1113_);
v___x_1115_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1116_ = lean_st_ref_get(v___y_1054_);
v_scopes_1137_ = lean_ctor_get(v___x_1116_, 2);
lean_inc(v_scopes_1137_);
lean_dec(v___x_1116_);
v___x_1138_ = l_List_head_x21___redArg(v___x_1115_, v_scopes_1137_);
lean_dec(v_scopes_1137_);
v_opts_1139_ = lean_ctor_get(v___x_1138_, 1);
lean_inc_ref(v_opts_1139_);
lean_dec(v___x_1138_);
v_hasTrace_1140_ = lean_ctor_get_uint8(v_opts_1139_, sizeof(void*)*1);
if (v_hasTrace_1140_ == 0)
{
lean_dec_ref(v_opts_1139_);
lean_dec(v___x_1114_);
lean_dec(v_hint_1052_);
lean_dec(v_mod_1050_);
v___y_1090_ = v___y_1054_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__9);
v___x_1142_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1114_, v_opts_1139_, v___x_1141_);
lean_dec_ref(v_opts_1139_);
lean_dec(v___x_1114_);
if (v___x_1142_ == 0)
{
lean_dec(v_hint_1052_);
lean_dec(v_mod_1050_);
v___y_1090_ = v___y_1054_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1143_; lean_object* v___y_1145_; 
v___x_1143_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__11);
if (v_isExporting_1078_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__16));
v___y_1145_ = v___x_1152_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__17));
v___y_1145_ = v___x_1153_;
goto v___jp_1144_;
}
v___jp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc_ref(v___y_1145_);
v___x_1146_ = l_Lean_stringToMessageData(v___y_1145_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1143_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__13);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
if (v_isMeta_1051_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__14));
v___y_1123_ = v___x_1149_;
v___y_1124_ = v___x_1150_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__15));
v___y_1123_ = v___x_1149_;
v___y_1124_ = v___x_1151_;
goto v___jp_1122_;
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v_toEnvExtension_1092_; lean_object* v_env_1093_; lean_object* v_messages_1094_; lean_object* v_scopes_1095_; lean_object* v_usedQuotCtxts_1096_; lean_object* v_nextMacroScope_1097_; lean_object* v_maxRecDepth_1098_; lean_object* v_ngen_1099_; lean_object* v_auxDeclNGen_1100_; lean_object* v_infoState_1101_; lean_object* v_traceState_1102_; lean_object* v_snapshotTasks_1103_; lean_object* v_prevLinterStates_1104_; lean_object* v_codeQualityEntryTasks_1105_; lean_object* v_asyncMode_1106_; uint8_t v_logWrites_1107_; lean_object* v___x_1108_; 
v___x_1091_ = lean_st_ref_take(v___y_1090_);
v_toEnvExtension_1092_ = lean_ctor_get(v___x_1082_, 0);
v_env_1093_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_env_1093_);
v_messages_1094_ = lean_ctor_get(v___x_1091_, 1);
lean_inc_ref(v_messages_1094_);
v_scopes_1095_ = lean_ctor_get(v___x_1091_, 2);
lean_inc(v_scopes_1095_);
v_usedQuotCtxts_1096_ = lean_ctor_get(v___x_1091_, 3);
lean_inc(v_usedQuotCtxts_1096_);
v_nextMacroScope_1097_ = lean_ctor_get(v___x_1091_, 4);
lean_inc(v_nextMacroScope_1097_);
v_maxRecDepth_1098_ = lean_ctor_get(v___x_1091_, 5);
lean_inc(v_maxRecDepth_1098_);
v_ngen_1099_ = lean_ctor_get(v___x_1091_, 6);
lean_inc_ref(v_ngen_1099_);
v_auxDeclNGen_1100_ = lean_ctor_get(v___x_1091_, 7);
lean_inc_ref(v_auxDeclNGen_1100_);
v_infoState_1101_ = lean_ctor_get(v___x_1091_, 8);
lean_inc_ref(v_infoState_1101_);
v_traceState_1102_ = lean_ctor_get(v___x_1091_, 9);
lean_inc_ref(v_traceState_1102_);
v_snapshotTasks_1103_ = lean_ctor_get(v___x_1091_, 10);
lean_inc_ref(v_snapshotTasks_1103_);
v_prevLinterStates_1104_ = lean_ctor_get(v___x_1091_, 11);
lean_inc(v_prevLinterStates_1104_);
v_codeQualityEntryTasks_1105_ = lean_ctor_get(v___x_1091_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1105_);
lean_dec(v___x_1091_);
v_asyncMode_1106_ = lean_ctor_get(v_toEnvExtension_1092_, 2);
v_logWrites_1107_ = lean_ctor_get_uint8(v_toEnvExtension_1092_, sizeof(void*)*6);
v___x_1108_ = lean_box(0);
if (v_logWrites_1107_ == 0)
{
lean_object* v___x_1109_; 
lean_inc_ref(v_toEnvExtension_1092_);
v___x_1109_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1092_, v_env_1093_, v___f_1087_, v_asyncMode_1106_, v___x_1084_, v___x_1088_);
v___y_1057_ = v_ngen_1099_;
v___y_1058_ = v_usedQuotCtxts_1096_;
v___y_1059_ = v_prevLinterStates_1104_;
v___y_1060_ = v_traceState_1102_;
v___y_1061_ = v_snapshotTasks_1103_;
v___y_1062_ = v_maxRecDepth_1098_;
v___y_1063_ = v_scopes_1095_;
v___y_1064_ = v_codeQualityEntryTasks_1105_;
v___y_1065_ = v_auxDeclNGen_1100_;
v___y_1066_ = v___y_1090_;
v___y_1067_ = v_messages_1094_;
v___y_1068_ = v_nextMacroScope_1097_;
v___y_1069_ = v_infoState_1101_;
v___y_1070_ = v___x_1108_;
v___y_1071_ = v___x_1109_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc_ref_n(v_toEnvExtension_1092_, 2);
v___x_1110_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1092_, v_env_1093_);
lean_dec_ref(v_env_1093_);
v___x_1111_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1092_, v___x_1110_, v___f_1087_, v_asyncMode_1106_, v___x_1084_, v___x_1088_);
v___y_1057_ = v_ngen_1099_;
v___y_1058_ = v_usedQuotCtxts_1096_;
v___y_1059_ = v_prevLinterStates_1104_;
v___y_1060_ = v_traceState_1102_;
v___y_1061_ = v_snapshotTasks_1103_;
v___y_1062_ = v_maxRecDepth_1098_;
v___y_1063_ = v_scopes_1095_;
v___y_1064_ = v_codeQualityEntryTasks_1105_;
v___y_1065_ = v_auxDeclNGen_1100_;
v___y_1066_ = v___y_1090_;
v___y_1067_ = v_messages_1094_;
v___y_1068_ = v_nextMacroScope_1097_;
v___y_1069_ = v_infoState_1101_;
v___y_1070_ = v___x_1108_;
v___y_1071_ = v___x_1111_;
goto v___jp_1056_;
}
}
v___jp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___y_1118_);
lean_ctor_set(v___x_1120_, 1, v___y_1119_);
v___x_1121_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_cls_1112_, v___x_1120_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_dec_ref_known(v___x_1121_, 1);
v___y_1090_ = v___y_1054_;
goto v___jp_1089_;
}
else
{
lean_dec_ref(v___f_1087_);
return v___x_1121_;
}
}
v___jp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
lean_inc_ref(v___y_1124_);
v___x_1125_ = l_Lean_stringToMessageData(v___y_1124_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1123_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__4);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_ofName(v_mod_1050_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_Name_isAnonymous(v_hint_1052_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__6);
v___x_1133_ = l_Lean_MessageData_ofName(v_hint_1052_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___y_1118_ = v___x_1130_;
v___y_1119_ = v___x_1134_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_hint_1052_);
v___x_1135_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1___closed__0));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
v___y_1118_ = v___x_1130_;
v___y_1119_ = v___x_1136_;
goto v___jp_1117_;
}
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref_known(v_entry_1079_, 1);
lean_dec(v_hint_1052_);
lean_dec(v_mod_1050_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
v___jp_1056_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1072_, 0, v___y_1071_);
lean_ctor_set(v___x_1072_, 1, v___y_1067_);
lean_ctor_set(v___x_1072_, 2, v___y_1063_);
lean_ctor_set(v___x_1072_, 3, v___y_1058_);
lean_ctor_set(v___x_1072_, 4, v___y_1068_);
lean_ctor_set(v___x_1072_, 5, v___y_1062_);
lean_ctor_set(v___x_1072_, 6, v___y_1057_);
lean_ctor_set(v___x_1072_, 7, v___y_1065_);
lean_ctor_set(v___x_1072_, 8, v___y_1069_);
lean_ctor_set(v___x_1072_, 9, v___y_1060_);
lean_ctor_set(v___x_1072_, 10, v___y_1061_);
lean_ctor_set(v___x_1072_, 11, v___y_1059_);
lean_ctor_set(v___x_1072_, 12, v___y_1064_);
v___x_1073_ = lean_st_ref_put(v___y_1066_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___y_1070_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___boxed(lean_object* v_mod_1156_, lean_object* v_isMeta_1157_, lean_object* v_hint_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v_isMeta_boxed_1162_; lean_object* v_res_1163_; 
v_isMeta_boxed_1162_ = lean_unbox(v_isMeta_1157_);
v_res_1163_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_mod_1156_, v_isMeta_boxed_1162_, v_hint_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(lean_object* v___x_1164_, lean_object* v_declName_1165_, lean_object* v_as_1166_, size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec(v_declName_1165_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_b_1169_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v_modules_1176_; lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v_toImport_1180_; lean_object* v_module_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1175_ = l_Lean_Environment_header(v___x_1164_);
v_modules_1176_ = lean_ctor_get(v___x_1175_, 3);
lean_inc_ref(v_modules_1176_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1178_ = lean_array_uget_borrowed(v_as_1166_, v_i_1168_);
v___x_1179_ = lean_array_get(v___x_1177_, v_modules_1176_, v_a_1178_);
lean_dec_ref(v_modules_1176_);
v_toImport_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_toImport_1180_);
lean_dec(v___x_1179_);
v_module_1181_ = lean_ctor_get(v_toImport_1180_, 0);
lean_inc(v_module_1181_);
lean_dec_ref(v_toImport_1180_);
v___x_1182_ = lean_box(0);
v___x_1183_ = 0;
lean_inc(v_declName_1165_);
v___x_1184_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1181_, v___x_1183_, v_declName_1165_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1184_) == 0)
{
size_t v___x_1185_; size_t v___x_1186_; 
lean_dec_ref_known(v___x_1184_, 1);
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1168_, v___x_1185_);
v_i_1168_ = v___x_1186_;
v_b_1169_ = v___x_1182_;
goto _start;
}
else
{
lean_dec(v_declName_1165_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6___boxed(lean_object* v___x_1188_, lean_object* v_declName_1189_, lean_object* v_as_1190_, lean_object* v_sz_1191_, lean_object* v_i_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v___x_1188_, v_declName_1189_, v_as_1190_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_as_1190_);
lean_dec_ref(v___x_1188_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_a_1200_, lean_object* v_x_1201_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
else
{
lean_object* v_key_1203_; lean_object* v_value_1204_; lean_object* v_tail_1205_; uint8_t v___x_1206_; 
v_key_1203_ = lean_ctor_get(v_x_1201_, 0);
v_value_1204_ = lean_ctor_get(v_x_1201_, 1);
v_tail_1205_ = lean_ctor_get(v_x_1201_, 2);
v___x_1206_ = lean_name_eq(v_key_1203_, v_a_1200_);
if (v___x_1206_ == 0)
{
v_x_1201_ = v_tail_1205_;
goto _start;
}
else
{
lean_object* v___x_1208_; 
lean_inc(v_value_1204_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_value_1204_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_a_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1209_, v_x_1210_);
lean_dec(v_x_1210_);
lean_dec(v_a_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(lean_object* v_m_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_buckets_1214_; lean_object* v___x_1215_; uint64_t v___y_1217_; 
v_buckets_1214_ = lean_ctor_get(v_m_1212_, 1);
v___x_1215_ = lean_array_get_size(v_buckets_1214_);
if (lean_obj_tag(v_a_1213_) == 0)
{
uint64_t v___x_1231_; 
v___x_1231_ = 1723ULL;
v___y_1217_ = v___x_1231_;
goto v___jp_1216_;
}
else
{
uint64_t v_hash_1232_; 
v_hash_1232_ = lean_ctor_get_uint64(v_a_1213_, sizeof(void*)*2);
v___y_1217_ = v_hash_1232_;
goto v___jp_1216_;
}
v___jp_1216_:
{
uint64_t v___x_1218_; uint64_t v___x_1219_; uint64_t v_fold_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1218_ = 32ULL;
v___x_1219_ = lean_uint64_shift_right(v___y_1217_, v___x_1218_);
v_fold_1220_ = lean_uint64_xor(v___y_1217_, v___x_1219_);
v___x_1221_ = 16ULL;
v___x_1222_ = lean_uint64_shift_right(v_fold_1220_, v___x_1221_);
v___x_1223_ = lean_uint64_xor(v_fold_1220_, v___x_1222_);
v___x_1224_ = lean_uint64_to_usize(v___x_1223_);
v___x_1225_ = lean_usize_of_nat(v___x_1215_);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_sub(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_usize_land(v___x_1224_, v___x_1227_);
v___x_1229_ = lean_array_uget_borrowed(v_buckets_1214_, v___x_1228_);
v___x_1230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_1213_, v___x_1229_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_m_1233_);
return v_res_1235_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(lean_object* v_declName_1239_, uint8_t v_isMeta_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_env_1249_; lean_object* v___y_1251_; lean_object* v___x_1264_; 
v___x_1244_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__0);
v___x_1245_ = lean_st_ref_get(v___y_1242_);
v_env_1249_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_env_1249_);
lean_dec(v___x_1245_);
v___x_1264_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1249_, v_declName_1239_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec_ref(v_env_1249_);
lean_dec(v_declName_1239_);
goto v___jp_1246_;
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1266_; lean_object* v_modules_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_val_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = l_Lean_Environment_header(v_env_1249_);
v_modules_1267_ = lean_ctor_get(v___x_1266_, 3);
lean_inc_ref(v_modules_1267_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = lean_array_get_size(v_modules_1267_);
v___x_1269_ = lean_nat_dec_lt(v_val_1265_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_dec_ref(v_modules_1267_);
lean_dec(v_val_1265_);
lean_dec_ref(v_env_1249_);
lean_dec(v_declName_1239_);
goto v___jp_1246_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___y_1273_; 
v___x_1270_ = lean_array_fget(v_modules_1267_, v_val_1265_);
lean_dec(v_val_1265_);
lean_dec_ref(v_modules_1267_);
v___x_1271_ = lean_st_ref_get(v___y_1242_);
if (v_isMeta_1240_ == 0)
{
lean_dec(v___x_1271_);
v___y_1273_ = v_isMeta_1240_;
goto v___jp_1272_;
}
else
{
lean_object* v_env_1284_; uint8_t v___x_1285_; 
v_env_1284_ = lean_ctor_get(v___x_1271_, 0);
lean_inc_ref(v_env_1284_);
lean_dec(v___x_1271_);
lean_inc(v_declName_1239_);
v___x_1285_ = l_Lean_isMarkedMeta(v_env_1284_, v_declName_1239_);
if (v___x_1285_ == 0)
{
v___y_1273_ = v_isMeta_1240_;
goto v___jp_1272_;
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = 0;
v___y_1273_ = v___x_1286_;
goto v___jp_1272_;
}
}
v___jp_1272_:
{
lean_object* v_toImport_1274_; lean_object* v_module_1275_; lean_object* v___x_1276_; 
v_toImport_1274_ = lean_ctor_get(v___x_1270_, 0);
lean_inc_ref(v_toImport_1274_);
lean_dec(v___x_1270_);
v_module_1275_ = lean_ctor_get(v_toImport_1274_, 0);
lean_inc(v_module_1275_);
lean_dec_ref(v_toImport_1274_);
lean_inc(v_declName_1239_);
v___x_1276_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5(v_module_1275_, v___y_1273_, v_declName_1239_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1276_, 1);
v___x_1277_ = l_Lean_indirectModUseExt;
v___x_1278_ = lean_box(1);
v___x_1279_ = lean_box(0);
lean_inc_ref(v_env_1249_);
v___x_1280_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1244_, v___x_1277_, v_env_1249_, v___x_1278_, v___x_1279_);
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v___x_1280_, v_declName_1239_);
lean_dec(v___x_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___closed__1));
v___y_1251_ = v___x_1282_;
goto v___jp_1250_;
}
else
{
lean_object* v_val_1283_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1281_, 1);
v___y_1251_ = v_val_1283_;
goto v___jp_1250_;
}
}
else
{
lean_dec_ref(v_env_1249_);
lean_dec(v_declName_1239_);
return v___x_1276_;
}
}
}
}
v___jp_1246_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
v___jp_1250_:
{
lean_object* v___x_1252_; size_t v_sz_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_box(0);
v_sz_1253_ = lean_array_size(v___y_1251_);
v___x_1254_ = ((size_t)0ULL);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__6(v_env_1249_, v_declName_1239_, v___y_1251_, v_sz_1253_, v___x_1254_, v___x_1252_, v___y_1241_, v___y_1242_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v_env_1249_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1263_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1252_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1252_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4___boxed(lean_object* v_declName_1287_, lean_object* v_isMeta_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
uint8_t v_isMeta_boxed_1292_; lean_object* v_res_1293_; 
v_isMeta_boxed_1292_ = lean_unbox(v_isMeta_1288_);
v_res_1293_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_declName_1287_, v_isMeta_boxed_1292_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(lean_object* v_as_x27_1294_, lean_object* v_b_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
if (lean_obj_tag(v_as_x27_1294_) == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_b_1295_);
return v___x_1299_;
}
else
{
lean_object* v_head_1300_; lean_object* v_tail_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; 
v_head_1300_ = lean_ctor_get(v_as_x27_1294_, 0);
v_tail_1301_ = lean_ctor_get(v_as_x27_1294_, 1);
v___x_1302_ = lean_box(0);
v___x_1303_ = 1;
lean_inc(v_head_1300_);
v___x_1304_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4(v_head_1300_, v___x_1303_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_dec_ref_known(v___x_1304_, 1);
v_as_x27_1294_ = v_tail_1301_;
v_b_1295_ = v___x_1302_;
goto _start;
}
else
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_1306_, v_b_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_as_x27_1306_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(lean_object* v_env_1312_, lean_object* v_currNamespace_1313_, lean_object* v_openDecls_1314_, lean_object* v_n_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = l_Lean_ResolveName_resolveNamespace(v_env_1312_, v_currNamespace_1313_, v_openDecls_1314_, v_n_1315_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed(lean_object* v_env_1320_, lean_object* v_currNamespace_1321_, lean_object* v_openDecls_1322_, lean_object* v_n_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4(v_env_1320_, v_currNamespace_1321_, v_openDecls_1322_, v_n_1323_, v___y_1324_, v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(lean_object* v_ref_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Elab_Command_getRef___redArg(v___y_1329_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v_fileName_1334_; lean_object* v_fileMap_1335_; lean_object* v_currRecDepth_1336_; lean_object* v_cmdPos_1337_; lean_object* v_macroStack_1338_; lean_object* v_quotContext_x3f_1339_; lean_object* v_currMacroScope_1340_; lean_object* v_snap_x3f_1341_; lean_object* v_cancelTk_x3f_1342_; uint8_t v_suppressElabErrors_1343_; uint8_t v_checkDeprecated_1344_; lean_object* v_ref_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v_fileName_1334_ = lean_ctor_get(v___y_1329_, 0);
v_fileMap_1335_ = lean_ctor_get(v___y_1329_, 1);
v_currRecDepth_1336_ = lean_ctor_get(v___y_1329_, 2);
v_cmdPos_1337_ = lean_ctor_get(v___y_1329_, 3);
v_macroStack_1338_ = lean_ctor_get(v___y_1329_, 4);
v_quotContext_x3f_1339_ = lean_ctor_get(v___y_1329_, 5);
v_currMacroScope_1340_ = lean_ctor_get(v___y_1329_, 6);
v_snap_x3f_1341_ = lean_ctor_get(v___y_1329_, 8);
v_cancelTk_x3f_1342_ = lean_ctor_get(v___y_1329_, 9);
v_suppressElabErrors_1343_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*10);
v_checkDeprecated_1344_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*10 + 1);
v_ref_1345_ = l_Lean_replaceRef(v_ref_1327_, v_a_1333_);
lean_dec(v_a_1333_);
lean_inc(v_cancelTk_x3f_1342_);
lean_inc(v_snap_x3f_1341_);
lean_inc(v_currMacroScope_1340_);
lean_inc(v_quotContext_x3f_1339_);
lean_inc(v_macroStack_1338_);
lean_inc(v_cmdPos_1337_);
lean_inc(v_currRecDepth_1336_);
lean_inc_ref(v_fileMap_1335_);
lean_inc_ref(v_fileName_1334_);
v___x_1346_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1346_, 0, v_fileName_1334_);
lean_ctor_set(v___x_1346_, 1, v_fileMap_1335_);
lean_ctor_set(v___x_1346_, 2, v_currRecDepth_1336_);
lean_ctor_set(v___x_1346_, 3, v_cmdPos_1337_);
lean_ctor_set(v___x_1346_, 4, v_macroStack_1338_);
lean_ctor_set(v___x_1346_, 5, v_quotContext_x3f_1339_);
lean_ctor_set(v___x_1346_, 6, v_currMacroScope_1340_);
lean_ctor_set(v___x_1346_, 7, v_ref_1345_);
lean_ctor_set(v___x_1346_, 8, v_snap_x3f_1341_);
lean_ctor_set(v___x_1346_, 9, v_cancelTk_x3f_1342_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*10, v_suppressElabErrors_1343_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*10 + 1, v_checkDeprecated_1344_);
v___x_1347_ = l_Lean_throwError___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__2___redArg(v_msg_1328_, v___x_1346_, v___y_1330_);
lean_dec_ref_known(v___x_1346_, 10);
return v___x_1347_;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v_msg_1328_);
v_a_1348_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1332_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1332_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1356_, lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_1356_, v_msg_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_ref_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(lean_object* v_currNamespace_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_currNamespace_1362_);
lean_ctor_set(v___x_1365_, 1, v___y_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed(lean_object* v_currNamespace_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3(v_currNamespace_1366_, v___y_1367_, v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(lean_object* v_x_1370_, lean_object* v___y_1371_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; 
v_a_1372_ = lean_ctor_get(v_x_1370_, 0);
lean_inc(v_a_1372_);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1372_);
lean_ctor_set(v___x_1373_, 1, v___y_1371_);
return v___x_1373_;
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v_x_1370_, 0);
lean_inc(v_a_1374_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1374_);
lean_ctor_set(v___x_1375_, 1, v___y_1371_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg___boxed(lean_object* v_x_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_1376_, v___y_1377_);
lean_dec_ref(v_x_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(lean_object* v_env_1379_, lean_object* v_stx_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1379_, v_stx_1380_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
if (lean_obj_tag(v_a_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1393_; 
v_a_1385_ = lean_ctor_get(v___x_1383_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1383_, 0);
lean_dec(v_unused_1394_);
v___x_1387_ = v___x_1383_;
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = lean_box(0);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1391_ = v___x_1387_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_a_1385_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_val_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1423_; 
v_val_1395_ = lean_ctor_get(v_a_1384_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_a_1384_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1397_ = v_a_1384_;
v_isShared_1398_ = v_isSharedCheck_1423_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_val_1395_);
lean_dec(v_a_1384_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1423_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_snd_1399_; 
v_snd_1399_ = lean_ctor_get(v_val_1395_, 1);
lean_inc(v_snd_1399_);
lean_dec(v_val_1395_);
if (lean_obj_tag(v_snd_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1397_);
v_a_1400_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1383_, 2);
v_a_1401_ = lean_ctor_get(v_snd_1399_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_snd_1399_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1403_ = v_snd_1399_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v_snd_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1406_, v_a_1400_);
lean_dec_ref(v___x_1406_);
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1422_; 
v_a_1410_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1383_, 2);
v_a_1411_ = lean_ctor_get(v_snd_1399_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_snd_1399_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1413_ = v_snd_1399_;
v_isShared_1414_ = v_isSharedCheck_1422_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v_snd_1399_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1422_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_a_1411_);
v___x_1416_ = v___x_1397_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v___x_1418_, v_a_1410_);
lean_dec_ref(v___x_1418_);
return v___x_1419_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1424_ = lean_ctor_get(v___x_1383_, 0);
v_a_1425_ = lean_ctor_get(v___x_1383_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1383_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_inc(v_a_1424_);
lean_dec(v___x_1383_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1424_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed(lean_object* v_env_1433_, lean_object* v_stx_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2(v_env_1433_, v_stx_1434_, v___y_1435_, v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(lean_object* v_env_1438_, lean_object* v_nm_1439_){
_start:
{
uint8_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = 1;
v___x_1441_ = l_Lean_Environment_contains(v_env_1438_, v_nm_1439_, v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0___boxed(lean_object* v_env_1442_, lean_object* v_nm_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1442_, v_nm_1443_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(lean_object* v_env_1446_, lean_object* v_declName_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v___x_1450_; lean_object* v_env_1451_; uint8_t v___x_1452_; 
v___x_1450_ = 0;
v_env_1451_ = l_Lean_Environment_setExporting(v_env_1446_, v___x_1450_);
lean_inc(v_declName_1447_);
lean_inc_ref(v_env_1451_);
v___x_1452_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1451_, v_declName_1447_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_inc(v_declName_1447_);
v___x_1453_ = l_Lean_mkPrivateName(v_env_1451_, v_declName_1447_);
lean_inc_ref(v_env_1451_);
v___x_1454_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1451_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_privateToUserName_x3f(v_declName_1447_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_env_1451_);
v___x_1456_ = lean_box(v___x_1454_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v___y_1449_);
return v___x_1457_;
}
else
{
lean_object* v_val_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_val_1458_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1459_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__0(v_env_1451_, v_val_1458_);
v___x_1460_ = lean_box(v___x_1459_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___y_1449_);
return v___x_1461_;
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_env_1451_);
lean_dec(v_declName_1447_);
v___x_1462_ = lean_box(v___x_1454_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___y_1449_);
return v___x_1463_;
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec_ref(v_env_1451_);
lean_dec(v_declName_1447_);
v___x_1464_ = lean_box(v___x_1452_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
lean_ctor_set(v___x_1465_, 1, v___y_1449_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed(lean_object* v_env_1466_, lean_object* v_declName_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1(v_env_1466_, v_declName_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1470_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg(){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___closed__0);
v___x_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg___boxed(lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__5(lean_object* v_env_1479_, lean_object* v_opts_1480_, lean_object* v_currNamespace_1481_, lean_object* v_openDecls_1482_, lean_object* v_n_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = l_Lean_ResolveName_resolveGlobalName(v_env_1479_, v_opts_1480_, v_currNamespace_1481_, v_openDecls_1482_, v_n_1483_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___y_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__5___boxed(lean_object* v_env_1488_, lean_object* v_opts_1489_, lean_object* v_currNamespace_1490_, lean_object* v_openDecls_1491_, lean_object* v_n_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__5(v_env_1488_, v_opts_1489_, v_currNamespace_1490_, v_openDecls_1491_, v_n_1492_, v___y_1493_, v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec_ref(v_opts_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(lean_object* v_as_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
if (lean_obj_tag(v_as_1496_) == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
else
{
lean_object* v_head_1502_; lean_object* v_tail_1503_; lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_scopes_1510_; lean_object* v___x_1511_; lean_object* v_opts_1512_; uint8_t v_hasTrace_1513_; 
v_head_1502_ = lean_ctor_get(v_as_1496_, 0);
lean_inc(v_head_1502_);
v_tail_1503_ = lean_ctor_get(v_as_1496_, 1);
lean_inc(v_tail_1503_);
lean_dec_ref_known(v_as_1496_, 2);
v_fst_1504_ = lean_ctor_get(v_head_1502_, 0);
lean_inc(v_fst_1504_);
v_snd_1505_ = lean_ctor_get(v_head_1502_, 1);
lean_inc(v_snd_1505_);
lean_dec(v_head_1502_);
v___x_1506_ = l_Lean_inheritedTraceOptions;
v___x_1507_ = lean_st_ref_get(v___x_1506_);
v___x_1508_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1509_ = lean_st_ref_get(v___y_1498_);
v_scopes_1510_ = lean_ctor_get(v___x_1509_, 2);
lean_inc(v_scopes_1510_);
lean_dec(v___x_1509_);
v___x_1511_ = l_List_head_x21___redArg(v___x_1508_, v_scopes_1510_);
lean_dec(v_scopes_1510_);
v_opts_1512_ = lean_ctor_get(v___x_1511_, 1);
lean_inc_ref(v_opts_1512_);
lean_dec(v___x_1511_);
v_hasTrace_1513_ = lean_ctor_get_uint8(v_opts_1512_, sizeof(void*)*1);
if (v_hasTrace_1513_ == 0)
{
lean_dec_ref(v_opts_1512_);
lean_dec(v___x_1507_);
lean_dec(v_snd_1505_);
lean_dec(v_fst_1504_);
v_as_1496_ = v_tail_1503_;
goto _start;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5___closed__8));
lean_inc(v_fst_1504_);
v___x_1516_ = l_Lean_Name_append(v___x_1515_, v_fst_1504_);
v___x_1517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1507_, v_opts_1512_, v___x_1516_);
lean_dec(v___x_1516_);
lean_dec_ref(v_opts_1512_);
lean_dec(v___x_1507_);
if (v___x_1517_ == 0)
{
lean_dec(v_snd_1505_);
lean_dec(v_fst_1504_);
v_as_1496_ = v_tail_1503_;
goto _start;
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_snd_1505_);
v___x_1520_ = l_Lean_MessageData_ofFormat(v___x_1519_);
v___x_1521_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__2(v_fst_1504_, v___x_1520_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_dec_ref_known(v___x_1521_, 1);
v_as_1496_ = v_tail_1503_;
goto _start;
}
else
{
lean_dec(v_tail_1503_);
return v___x_1521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6___boxed(lean_object* v_as_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v_as_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v_env_1534_; lean_object* v___f_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_scopes_1539_; lean_object* v___x_1540_; lean_object* v_opts_1541_; lean_object* v___x_1542_; 
v___x_1533_ = lean_st_ref_get(v___y_1531_);
v_env_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_ref_n(v_env_1534_, 3);
lean_dec(v___x_1533_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1535_, 0, v_env_1534_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1536_, 0, v_env_1534_);
v___x_1537_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1538_ = lean_st_ref_get(v___y_1531_);
v_scopes_1539_ = lean_ctor_get(v___x_1538_, 2);
lean_inc(v_scopes_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = l_List_head_x21___redArg(v___x_1537_, v_scopes_1539_);
lean_dec(v_scopes_1539_);
v_opts_1541_ = lean_ctor_get(v___x_1540_, 1);
lean_inc_ref(v_opts_1541_);
lean_dec(v___x_1540_);
v___x_1542_ = l_Lean_Elab_Command_getScope___redArg(v___y_1531_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_currNamespace_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_currNamespace_1544_ = lean_ctor_get(v_a_1543_, 2);
lean_inc_n(v_currNamespace_1544_, 2);
lean_dec(v_a_1543_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1545_, 0, v_currNamespace_1544_);
v___x_1546_ = l_Lean_Elab_Command_getScope___redArg(v___y_1531_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_openDecls_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v_methods_1551_; lean_object* v___x_1552_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v_openDecls_1548_ = lean_ctor_get(v_a_1547_, 3);
lean_inc_n(v_openDecls_1548_, 2);
lean_dec(v_a_1547_);
lean_inc(v_currNamespace_1544_);
lean_inc_ref(v_env_1534_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1549_, 0, v_env_1534_);
lean_closure_set(v___f_1549_, 1, v_currNamespace_1544_);
lean_closure_set(v___f_1549_, 2, v_openDecls_1548_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___lam__5___boxed), 7, 4);
lean_closure_set(v___f_1550_, 0, v_env_1534_);
lean_closure_set(v___f_1550_, 1, v_opts_1541_);
lean_closure_set(v___f_1550_, 2, v_currNamespace_1544_);
lean_closure_set(v___f_1550_, 3, v_openDecls_1548_);
v_methods_1551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1551_, 0, v___f_1536_);
lean_ctor_set(v_methods_1551_, 1, v___f_1545_);
lean_ctor_set(v_methods_1551_, 2, v___f_1535_);
lean_ctor_set(v_methods_1551_, 3, v___f_1549_);
lean_ctor_set(v_methods_1551_, 4, v___f_1550_);
v___x_1552_ = l_Lean_Elab_Command_getRef___redArg(v___y_1530_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1530_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v_currRecDepth_1556_; lean_object* v_quotContext_x3f_1557_; lean_object* v_a_1559_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_currRecDepth_1556_ = lean_ctor_get(v___y_1530_, 2);
v_quotContext_x3f_1557_ = lean_ctor_get(v___y_1530_, 5);
if (lean_obj_tag(v_quotContext_x3f_1557_) == 0)
{
lean_object* v___x_1633_; lean_object* v_a_1634_; 
v___x_1633_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_1531_);
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1633_);
v_a_1559_ = v_a_1634_;
goto v___jp_1558_;
}
else
{
lean_object* v_val_1635_; 
v_val_1635_ = lean_ctor_get(v_quotContext_x3f_1557_, 0);
lean_inc(v_val_1635_);
v_a_1559_ = v_val_1635_;
goto v___jp_1558_;
}
v___jp_1558_:
{
lean_object* v___x_1560_; lean_object* v_maxRecDepth_1561_; lean_object* v___x_1562_; lean_object* v_nextMacroScope_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1560_ = lean_st_ref_get(v___y_1531_);
v_maxRecDepth_1561_ = lean_ctor_get(v___x_1560_, 5);
lean_inc(v_maxRecDepth_1561_);
lean_dec(v___x_1560_);
v___x_1562_ = lean_st_ref_get(v___y_1531_);
v_nextMacroScope_1563_ = lean_ctor_get(v___x_1562_, 4);
lean_inc(v_nextMacroScope_1563_);
lean_dec(v___x_1562_);
lean_inc(v_currRecDepth_1556_);
v___x_1564_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1564_, 0, v_methods_1551_);
lean_ctor_set(v___x_1564_, 1, v_a_1559_);
lean_ctor_set(v___x_1564_, 2, v_a_1555_);
lean_ctor_set(v___x_1564_, 3, v_currRecDepth_1556_);
lean_ctor_set(v___x_1564_, 4, v_maxRecDepth_1561_);
lean_ctor_set(v___x_1564_, 5, v_a_1553_);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1566_, 0, v_nextMacroScope_1563_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
v___x_1567_ = lean_apply_2(v_x_1529_, v___x_1564_, v___x_1566_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v_macroScope_1570_; lean_object* v_traceMsgs_1571_; lean_object* v_expandedMacroDecls_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_a_1568_);
v_a_1569_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1567_, 2);
v_macroScope_1570_ = lean_ctor_get(v_a_1568_, 0);
lean_inc(v_macroScope_1570_);
v_traceMsgs_1571_ = lean_ctor_get(v_a_1568_, 1);
lean_inc(v_traceMsgs_1571_);
v_expandedMacroDecls_1572_ = lean_ctor_get(v_a_1568_, 2);
lean_inc(v_expandedMacroDecls_1572_);
lean_dec(v_a_1568_);
v___x_1573_ = lean_box(0);
v___x_1574_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_expandedMacroDecls_1572_, v___x_1573_, v___y_1530_, v___y_1531_);
lean_dec(v_expandedMacroDecls_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v_env_1576_; lean_object* v_messages_1577_; lean_object* v_scopes_1578_; lean_object* v_usedQuotCtxts_1579_; lean_object* v_maxRecDepth_1580_; lean_object* v_ngen_1581_; lean_object* v_auxDeclNGen_1582_; lean_object* v_infoState_1583_; lean_object* v_traceState_1584_; lean_object* v_snapshotTasks_1585_; lean_object* v_prevLinterStates_1586_; lean_object* v_codeQualityEntryTasks_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref_known(v___x_1574_, 1);
v___x_1575_ = lean_st_ref_take(v___y_1531_);
v_env_1576_ = lean_ctor_get(v___x_1575_, 0);
v_messages_1577_ = lean_ctor_get(v___x_1575_, 1);
v_scopes_1578_ = lean_ctor_get(v___x_1575_, 2);
v_usedQuotCtxts_1579_ = lean_ctor_get(v___x_1575_, 3);
v_maxRecDepth_1580_ = lean_ctor_get(v___x_1575_, 5);
v_ngen_1581_ = lean_ctor_get(v___x_1575_, 6);
v_auxDeclNGen_1582_ = lean_ctor_get(v___x_1575_, 7);
v_infoState_1583_ = lean_ctor_get(v___x_1575_, 8);
v_traceState_1584_ = lean_ctor_get(v___x_1575_, 9);
v_snapshotTasks_1585_ = lean_ctor_get(v___x_1575_, 10);
v_prevLinterStates_1586_ = lean_ctor_get(v___x_1575_, 11);
v_codeQualityEntryTasks_1587_ = lean_ctor_get(v___x_1575_, 12);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1575_, 4);
lean_dec(v_unused_1614_);
v___x_1589_ = v___x_1575_;
v_isShared_1590_ = v_isSharedCheck_1613_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1587_);
lean_inc(v_prevLinterStates_1586_);
lean_inc(v_snapshotTasks_1585_);
lean_inc(v_traceState_1584_);
lean_inc(v_infoState_1583_);
lean_inc(v_auxDeclNGen_1582_);
lean_inc(v_ngen_1581_);
lean_inc(v_maxRecDepth_1580_);
lean_inc(v_usedQuotCtxts_1579_);
lean_inc(v_scopes_1578_);
lean_inc(v_messages_1577_);
lean_inc(v_env_1576_);
lean_dec(v___x_1575_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1613_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v_macroScope_1570_);
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_env_1576_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_messages_1577_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_scopes_1578_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_usedQuotCtxts_1579_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_macroScope_1570_);
lean_ctor_set(v_reuseFailAlloc_1612_, 5, v_maxRecDepth_1580_);
lean_ctor_set(v_reuseFailAlloc_1612_, 6, v_ngen_1581_);
lean_ctor_set(v_reuseFailAlloc_1612_, 7, v_auxDeclNGen_1582_);
lean_ctor_set(v_reuseFailAlloc_1612_, 8, v_infoState_1583_);
lean_ctor_set(v_reuseFailAlloc_1612_, 9, v_traceState_1584_);
lean_ctor_set(v_reuseFailAlloc_1612_, 10, v_snapshotTasks_1585_);
lean_ctor_set(v_reuseFailAlloc_1612_, 11, v_prevLinterStates_1586_);
lean_ctor_set(v_reuseFailAlloc_1612_, 12, v_codeQualityEntryTasks_1587_);
v___x_1592_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_st_ref_put(v___y_1531_, v___x_1592_);
v___x_1594_ = l_List_reverse___redArg(v_traceMsgs_1571_);
v___x_1595_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__6(v___x_1594_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v___x_1595_, 0);
lean_dec(v_unused_1603_);
v___x_1597_ = v___x_1595_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v___x_1595_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_a_1569_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1569_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1569_);
v_a_1604_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1595_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1595_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_traceMsgs_1571_);
lean_dec(v_macroScope_1570_);
lean_dec(v_a_1569_);
v_a_1615_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1574_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1574_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1623_; 
v_a_1623_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1567_, 2);
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_a_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v_a_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_a_1624_);
v_a_1625_ = lean_ctor_get(v_a_1623_, 1);
lean_inc_ref(v_a_1625_);
lean_dec_ref_known(v_a_1623_, 2);
v___x_1626_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___closed__0));
v___x_1627_ = lean_string_dec_eq(v_a_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_a_1625_);
v___x_1629_ = l_Lean_MessageData_ofFormat(v___x_1628_);
v___x_1630_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_a_1624_, v___x_1629_, v___y_1530_, v___y_1531_);
lean_dec(v_a_1624_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; 
lean_dec_ref(v_a_1625_);
v___x_1631_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_a_1624_);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_1632_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1553_);
lean_dec_ref_known(v_methods_1551_, 5);
lean_dec_ref(v_x_1529_);
v_a_1636_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1554_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1554_);
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
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref_known(v_methods_1551_, 5);
lean_dec_ref(v_x_1529_);
v_a_1644_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1552_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1552_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___f_1545_);
lean_dec(v_currNamespace_1544_);
lean_dec_ref(v_opts_1541_);
lean_dec_ref(v___f_1536_);
lean_dec_ref(v___f_1535_);
lean_dec_ref(v_env_1534_);
lean_dec_ref(v_x_1529_);
v_a_1652_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1546_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1546_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_opts_1541_);
lean_dec_ref(v___f_1536_);
lean_dec_ref(v___f_1535_);
lean_dec_ref(v_env_1534_);
lean_dec_ref(v_x_1529_);
v_a_1660_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1542_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1542_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg___boxed(lean_object* v_x_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1672_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__4));
v___x_1687_ = l_String_toRawSubstring_x27(v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1710_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__17));
v___x_1711_ = lean_unsigned_to_nat(14u);
v___x_1712_ = lean_unsigned_to_nat(22u);
v___x_1713_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__16));
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__15));
v___x_1715_ = l_mkPanicMessageWithDecl(v___x_1714_, v___x_1713_, v___x_1712_, v___x_1711_, v___x_1710_);
return v___x_1715_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__27));
v___x_1732_ = l_String_toRawSubstring_x27(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__37));
v___x_1745_ = l_Lean_mkAtom(v___x_1744_);
return v___x_1745_;
}
}
static lean_object* _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__39));
v___x_1748_ = l_Lean_mkAtom(v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(lean_object* v_id_x3f_1749_, lean_object* v_id_1750_, lean_object* v_stx_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_pat_1756_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__1));
lean_inc(v_stx_1751_);
v___x_1760_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__3));
lean_inc(v_stx_1751_);
v___x_1762_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v_a_1769_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v_a_1805_; uint8_t v___x_1836_; 
v___x_1763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
lean_inc(v_stx_1751_);
v___x_1836_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1763_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__10));
lean_inc(v_stx_1751_);
v___x_1838_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__12));
lean_inc(v_stx_1751_);
v___x_1840_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1839_);
if (v___x_1840_ == 0)
{
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_SourceInfo_fromRef(v_a_1842_, v___x_1840_);
lean_dec(v_a_1842_);
v___x_1844_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v_a_1847_; lean_object* v_quotContext_x3f_1878_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v_quotContext_x3f_1878_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_1878_) == 0)
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v_a_1847_ = v_a_1880_;
goto v___jp_1846_;
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1845_);
lean_dec(v___x_1843_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_1881_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1879_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1879_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v_val_1889_; 
v_val_1889_ = lean_ctor_get(v_quotContext_x3f_1878_, 0);
lean_inc(v_val_1889_);
v_a_1847_ = v_val_1889_;
goto v___jp_1846_;
}
v___jp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1848_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1849_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1850_ = l_Lean_addMacroScope(v_a_1847_, v___x_1849_, v_a_1845_);
v___x_1851_ = lean_box(0);
lean_inc_n(v___x_1843_, 4);
v___x_1852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1843_);
lean_ctor_set(v___x_1852_, 1, v___x_1848_);
lean_ctor_set(v___x_1852_, 2, v___x_1850_);
lean_ctor_set(v___x_1852_, 3, v___x_1851_);
v___x_1853_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1843_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_1856_ = l_Lean_Syntax_node1(v___x_1843_, v___x_1855_, v_stx_1751_);
v___x_1857_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1843_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_Syntax_node4(v___x_1843_, v___x_1763_, v___x_1852_, v___x_1854_, v___x_1856_, v___x_1858_);
v___x_1860_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1859_);
lean_ctor_set(v___x_1865_, 1, v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v___x_1859_);
v_a_1870_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1860_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1860_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v___x_1843_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_1890_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1844_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1844_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_1898_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1841_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1841_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_val_1906_; lean_object* v___x_1907_; 
lean_dec(v_id_1750_);
v_val_1906_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_1906_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_1907_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_1906_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v_pat_1756_ = v_a_1908_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_stx_1751_);
v_a_1909_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1907_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1907_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1917_);
lean_inc(v___x_1918_);
v___x_1919_ = l_Lean_Syntax_matchesNull(v___x_1918_, v___x_1917_);
if (v___x_1919_ == 0)
{
lean_dec(v___x_1918_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_SourceInfo_fromRef(v_a_1921_, v___x_1919_);
lean_dec(v_a_1921_);
v___x_1923_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v_a_1926_; lean_object* v_quotContext_x3f_1957_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_quotContext_x3f_1957_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_1957_) == 0)
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v_a_1926_ = v_a_1959_;
goto v___jp_1925_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec(v_a_1924_);
lean_dec(v___x_1922_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_1960_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_val_1968_; 
v_val_1968_ = lean_ctor_get(v_quotContext_x3f_1957_, 0);
lean_inc(v_val_1968_);
v_a_1926_ = v_val_1968_;
goto v___jp_1925_;
}
v___jp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1927_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1929_ = l_Lean_addMacroScope(v_a_1926_, v___x_1928_, v_a_1924_);
v___x_1930_ = lean_box(0);
lean_inc_n(v___x_1922_, 4);
v___x_1931_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1922_);
lean_ctor_set(v___x_1931_, 1, v___x_1927_);
lean_ctor_set(v___x_1931_, 2, v___x_1929_);
lean_ctor_set(v___x_1931_, 3, v___x_1930_);
v___x_1932_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1922_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_1935_ = l_Lean_Syntax_node1(v___x_1922_, v___x_1934_, v_stx_1751_);
v___x_1936_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1922_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_Syntax_node4(v___x_1922_, v___x_1763_, v___x_1931_, v___x_1933_, v___x_1935_, v___x_1937_);
v___x_1939_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1938_);
lean_ctor_set(v___x_1944_, 1, v_a_1940_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v___x_1938_);
v_a_1949_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1939_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1939_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v___x_1922_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_1969_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1923_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1923_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_1977_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1920_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1920_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_val_1985_; lean_object* v___x_1986_; 
lean_dec(v_id_1750_);
v_val_1985_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_1986_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_1985_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v_pat_1756_ = v_a_1987_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_stx_1751_);
v_a_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1996_ = lean_unsigned_to_nat(3u);
v___x_1997_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1996_);
v___x_1998_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_1997_);
v___x_1999_ = l_Lean_Syntax_isOfKind(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_dec(v___x_1997_);
lean_dec(v___x_1918_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = l_Lean_SourceInfo_fromRef(v_a_2001_, v___x_1838_);
lean_dec(v_a_2001_);
v___x_2003_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_a_2006_; lean_object* v_quotContext_x3f_2037_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v_quotContext_x3f_2037_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2037_) == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v_a_2006_ = v_a_2039_;
goto v___jp_2005_;
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_2004_);
lean_dec(v___x_2002_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2040_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2038_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2038_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_val_2048_; 
v_val_2048_ = lean_ctor_get(v_quotContext_x3f_2037_, 0);
lean_inc(v_val_2048_);
v_a_2006_ = v_val_2048_;
goto v___jp_2005_;
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2007_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2009_ = l_Lean_addMacroScope(v_a_2006_, v___x_2008_, v_a_2004_);
v___x_2010_ = lean_box(0);
lean_inc_n(v___x_2002_, 4);
v___x_2011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2002_);
lean_ctor_set(v___x_2011_, 1, v___x_2007_);
lean_ctor_set(v___x_2011_, 2, v___x_2009_);
lean_ctor_set(v___x_2011_, 3, v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2002_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2015_ = l_Lean_Syntax_node1(v___x_2002_, v___x_2014_, v_stx_1751_);
v___x_2016_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2002_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = l_Lean_Syntax_node4(v___x_2002_, v___x_1763_, v___x_2011_, v___x_2013_, v___x_2015_, v___x_2017_);
v___x_2019_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2018_);
lean_ctor_set(v___x_2024_, 1, v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_2018_);
v_a_2029_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2019_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2019_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_2002_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2049_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2003_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2003_);
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
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2057_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2000_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2000_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_val_2065_; lean_object* v___x_2066_; 
lean_dec(v_id_1750_);
v_val_2065_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2066_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2065_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v_pat_1756_ = v_a_2067_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_stx_1751_);
v_a_2068_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2066_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v_stx_2077_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___x_2103_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v_stx_2077_ = l_Lean_Syntax_getArg(v___x_1918_, v___x_2076_);
lean_dec(v___x_1918_);
v___x_2103_ = lean_unsigned_to_nat(2u);
v___x_2156_ = lean_unsigned_to_nat(4u);
v___x_2157_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2156_);
v___x_2158_ = l_Lean_Syntax_isNone(v___x_2157_);
if (v___x_2158_ == 0)
{
uint8_t v___x_2159_; 
lean_inc(v___x_2157_);
v___x_2159_ = l_Lean_Syntax_matchesNull(v___x_2157_, v___x_2103_);
if (v___x_2159_ == 0)
{
lean_dec(v___x_2157_);
lean_dec(v_stx_2077_);
lean_dec(v___x_1997_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = l_Lean_SourceInfo_fromRef(v_a_2161_, v___x_2159_);
lean_dec(v_a_2161_);
v___x_2163_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_a_2166_; lean_object* v_quotContext_x3f_2197_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_quotContext_x3f_2197_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2197_) == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v_a_2166_ = v_a_2199_;
goto v___jp_2165_;
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2164_);
lean_dec(v___x_2162_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2200_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2198_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_val_2208_; 
v_val_2208_ = lean_ctor_get(v_quotContext_x3f_2197_, 0);
lean_inc(v_val_2208_);
v_a_2166_ = v_val_2208_;
goto v___jp_2165_;
}
v___jp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2167_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2168_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2169_ = l_Lean_addMacroScope(v_a_2166_, v___x_2168_, v_a_2164_);
v___x_2170_ = lean_box(0);
lean_inc_n(v___x_2162_, 4);
v___x_2171_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2162_);
lean_ctor_set(v___x_2171_, 1, v___x_2167_);
lean_ctor_set(v___x_2171_, 2, v___x_2169_);
lean_ctor_set(v___x_2171_, 3, v___x_2170_);
v___x_2172_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2162_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2175_ = l_Lean_Syntax_node1(v___x_2162_, v___x_2174_, v_stx_1751_);
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2162_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_Syntax_node4(v___x_2162_, v___x_1763_, v___x_2171_, v___x_2173_, v___x_2175_, v___x_2177_);
v___x_2179_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2178_);
lean_ctor_set(v___x_2184_, 1, v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v___x_2178_);
v_a_2189_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2179_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v___x_2162_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2209_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2163_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2163_);
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
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2217_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2160_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2160_);
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
lean_object* v_val_2225_; lean_object* v___x_2226_; 
lean_dec(v_id_1750_);
v_val_2225_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2225_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2226_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2225_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v_pat_1756_ = v_a_2227_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_stx_1751_);
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
}
else
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = l_Lean_Syntax_getArg(v___x_2157_, v___x_1917_);
lean_dec(v___x_2157_);
v___x_2237_ = l_Lean_Syntax_matchesNull(v___x_2236_, v___x_1917_);
if (v___x_2237_ == 0)
{
lean_dec(v_stx_2077_);
lean_dec(v___x_1997_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l_Lean_SourceInfo_fromRef(v_a_2239_, v___x_2237_);
lean_dec(v_a_2239_);
v___x_2241_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v_a_2244_; lean_object* v_quotContext_x3f_2275_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v_quotContext_x3f_2275_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2275_) == 0)
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v_a_2244_ = v_a_2277_;
goto v___jp_2243_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2242_);
lean_dec(v___x_2240_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2278_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2276_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2276_);
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
else
{
lean_object* v_val_2286_; 
v_val_2286_ = lean_ctor_get(v_quotContext_x3f_2275_, 0);
lean_inc(v_val_2286_);
v_a_2244_ = v_val_2286_;
goto v___jp_2243_;
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2245_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2246_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2247_ = l_Lean_addMacroScope(v_a_2244_, v___x_2246_, v_a_2242_);
v___x_2248_ = lean_box(0);
lean_inc_n(v___x_2240_, 4);
v___x_2249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2240_);
lean_ctor_set(v___x_2249_, 1, v___x_2245_);
lean_ctor_set(v___x_2249_, 2, v___x_2247_);
lean_ctor_set(v___x_2249_, 3, v___x_2248_);
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2240_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2253_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2252_, v_stx_1751_);
v___x_2254_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2240_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_node4(v___x_2240_, v___x_1763_, v___x_2249_, v___x_2251_, v___x_2253_, v___x_2255_);
v___x_2257_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2266_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2256_);
lean_ctor_set(v___x_2262_, 1, v_a_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v___x_2256_);
v_a_2267_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2257_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2257_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v___x_2240_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2287_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2241_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2241_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2295_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2238_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2238_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_val_2303_; lean_object* v___x_2304_; 
lean_dec(v_id_1750_);
v_val_2303_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2304_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2303_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_pat_1756_ = v_a_2305_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v_stx_1751_);
v_a_2306_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2304_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2304_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
else
{
v___y_2105_ = v_a_1752_;
v___y_2106_ = v_a_1753_;
goto v___jp_2104_;
}
}
}
else
{
lean_dec(v___x_2157_);
v___y_2105_ = v_a_1752_;
v___y_2106_ = v_a_1753_;
goto v___jp_2104_;
}
v___jp_2078_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2084_ = lean_string_append(v___y_2082_, v___x_2083_);
lean_inc(v___y_2080_);
v___x_2085_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2080_, v_stx_2077_, v_id_1750_, v___x_2084_, v___y_2079_, v___y_2081_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v_pat_1756_ = v_a_2086_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_stx_1751_);
v_a_2087_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2085_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
v___jp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2099_ = l_Lean_Syntax_isStrLit_x3f(v___x_1997_);
lean_dec(v___x_1997_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2101_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2100_);
v___y_2079_ = v___y_2096_;
v___y_2080_ = v___x_2098_;
v___y_2081_ = v___y_2097_;
v___y_2082_ = v___x_2101_;
goto v___jp_2078_;
}
else
{
lean_object* v_val_2102_; 
v_val_2102_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v___x_2099_, 1);
v___y_2079_ = v___y_2096_;
v___y_2080_ = v___x_2098_;
v___y_2081_ = v___y_2097_;
v___y_2082_ = v_val_2102_;
goto v___jp_2078_;
}
}
v___jp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2107_ = lean_unsigned_to_nat(5u);
v___x_2108_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_isNone(v___x_2108_);
if (v___x_2109_ == 0)
{
uint8_t v___x_2110_; 
v___x_2110_ = l_Lean_Syntax_matchesNull(v___x_2108_, v___x_2103_);
if (v___x_2110_ == 0)
{
lean_dec(v_stx_2077_);
lean_dec(v___x_1997_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Elab_Command_getRef___redArg(v___y_2105_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_SourceInfo_fromRef(v_a_2112_, v___x_2110_);
lean_dec(v_a_2112_);
v___x_2114_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2105_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_quotContext_x3f_2115_; 
v_quotContext_x3f_2115_ = lean_ctor_get(v___y_2105_, 5);
if (lean_obj_tag(v_quotContext_x3f_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2117_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2106_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___y_1765_ = v___x_2113_;
v___y_1766_ = v___y_2106_;
v___y_1767_ = v_a_2116_;
v___y_1768_ = v___y_2105_;
v_a_1769_ = v_a_2118_;
goto v___jp_1764_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2116_);
lean_dec(v___x_2113_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2119_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2117_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2117_);
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
lean_object* v_a_2127_; lean_object* v_val_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2114_, 1);
v_val_2128_ = lean_ctor_get(v_quotContext_x3f_2115_, 0);
lean_inc(v_val_2128_);
v___y_1765_ = v___x_2113_;
v___y_1766_ = v___y_2106_;
v___y_1767_ = v_a_2127_;
v___y_1768_ = v___y_2105_;
v_a_1769_ = v_val_2128_;
goto v___jp_1764_;
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v___x_2113_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2129_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2114_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2114_);
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
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2137_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2111_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2111_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_val_2145_; lean_object* v___x_2146_; 
lean_dec(v_id_1750_);
v_val_2145_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2146_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2145_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v_pat_1756_ = v_a_2147_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_stx_1751_);
v_a_2148_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2146_);
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
lean_dec(v_id_x3f_1749_);
v___y_2096_ = v___y_2105_;
v___y_2097_ = v___y_2106_;
goto v___jp_2095_;
}
}
else
{
lean_dec(v___x_2108_);
lean_dec(v_id_x3f_1749_);
v___y_2096_ = v___y_2105_;
v___y_2097_ = v___y_2106_;
goto v___jp_2095_;
}
}
}
}
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2314_);
lean_inc(v___x_2315_);
v___x_2316_ = l_Lean_Syntax_matchesNull(v___x_2315_, v___x_2314_);
if (v___x_2316_ == 0)
{
lean_dec(v___x_2315_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = l_Lean_SourceInfo_fromRef(v_a_2318_, v___x_2316_);
lean_dec(v_a_2318_);
v___x_2320_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v_a_2323_; lean_object* v_quotContext_x3f_2354_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v_quotContext_x3f_2354_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2354_) == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v_a_2323_ = v_a_2356_;
goto v___jp_2322_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2321_);
lean_dec(v___x_2319_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
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
v_val_2365_ = lean_ctor_get(v_quotContext_x3f_2354_, 0);
lean_inc(v_val_2365_);
v_a_2323_ = v_val_2365_;
goto v___jp_2322_;
}
v___jp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2324_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2325_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2326_ = l_Lean_addMacroScope(v_a_2323_, v___x_2325_, v_a_2321_);
v___x_2327_ = lean_box(0);
lean_inc_n(v___x_2319_, 4);
v___x_2328_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2319_);
lean_ctor_set(v___x_2328_, 1, v___x_2324_);
lean_ctor_set(v___x_2328_, 2, v___x_2326_);
lean_ctor_set(v___x_2328_, 3, v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2319_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2332_ = l_Lean_Syntax_node1(v___x_2319_, v___x_2331_, v_stx_1751_);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2319_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node4(v___x_2319_, v___x_1763_, v___x_2328_, v___x_2330_, v___x_2332_, v___x_2334_);
v___x_2336_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2345_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2335_);
lean_ctor_set(v___x_2341_, 1, v_a_2337_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2341_);
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v___x_2335_);
v_a_2346_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2336_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2336_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___x_2319_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2366_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2320_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2320_);
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
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2374_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2317_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2317_);
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
lean_dec(v_id_1750_);
v_val_2382_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2383_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2382_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v_pat_1756_ = v_a_2384_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_stx_1751_);
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
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2393_ = lean_unsigned_to_nat(3u);
v___x_2394_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2393_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_2394_);
v___x_2396_ = l_Lean_Syntax_isOfKind(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec(v___x_2394_);
lean_dec(v___x_2315_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v___x_2399_ = l_Lean_SourceInfo_fromRef(v_a_2398_, v___x_1836_);
lean_dec(v_a_2398_);
v___x_2400_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v_a_2403_; lean_object* v_quotContext_x3f_2434_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v_quotContext_x3f_2434_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2434_) == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_a_2403_ = v_a_2436_;
goto v___jp_2402_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_a_2401_);
lean_dec(v___x_2399_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_val_2445_; 
v_val_2445_ = lean_ctor_get(v_quotContext_x3f_2434_, 0);
lean_inc(v_val_2445_);
v_a_2403_ = v_val_2445_;
goto v___jp_2402_;
}
v___jp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2406_ = l_Lean_addMacroScope(v_a_2403_, v___x_2405_, v_a_2401_);
v___x_2407_ = lean_box(0);
lean_inc_n(v___x_2399_, 4);
v___x_2408_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2399_);
lean_ctor_set(v___x_2408_, 1, v___x_2404_);
lean_ctor_set(v___x_2408_, 2, v___x_2406_);
lean_ctor_set(v___x_2408_, 3, v___x_2407_);
v___x_2409_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2399_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2412_ = l_Lean_Syntax_node1(v___x_2399_, v___x_2411_, v_stx_1751_);
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2399_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_Syntax_node4(v___x_2399_, v___x_1763_, v___x_2408_, v___x_2410_, v___x_2412_, v___x_2414_);
v___x_2416_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2425_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2415_);
lean_ctor_set(v___x_2421_, 1, v_a_2417_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2421_);
v___x_2423_ = v___x_2419_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v___x_2415_);
v_a_2426_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2416_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2416_);
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
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v___x_2399_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2446_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2400_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2400_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2454_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2397_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2397_);
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
else
{
lean_object* v_val_2462_; lean_object* v___x_2463_; 
lean_dec(v_id_1750_);
v_val_2462_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2463_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2462_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v_pat_1756_ = v_a_2464_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_stx_1751_);
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
}
else
{
lean_object* v___x_2473_; lean_object* v_stx_2474_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___x_2500_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2473_ = lean_unsigned_to_nat(0u);
v_stx_2474_ = l_Lean_Syntax_getArg(v___x_2315_, v___x_2473_);
lean_dec(v___x_2315_);
v___x_2500_ = lean_unsigned_to_nat(2u);
v___x_2553_ = lean_unsigned_to_nat(4u);
v___x_2554_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_isNone(v___x_2554_);
if (v___x_2555_ == 0)
{
uint8_t v___x_2556_; 
lean_inc(v___x_2554_);
v___x_2556_ = l_Lean_Syntax_matchesNull(v___x_2554_, v___x_2500_);
if (v___x_2556_ == 0)
{
lean_dec(v___x_2554_);
lean_dec(v_stx_2474_);
lean_dec(v___x_2394_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = l_Lean_SourceInfo_fromRef(v_a_2558_, v___x_2556_);
lean_dec(v_a_2558_);
v___x_2560_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v_a_2563_; lean_object* v_quotContext_x3f_2594_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v_quotContext_x3f_2594_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2594_) == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v_a_2563_ = v_a_2596_;
goto v___jp_2562_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_a_2561_);
lean_dec(v___x_2559_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2597_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2595_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_val_2605_; 
v_val_2605_ = lean_ctor_get(v_quotContext_x3f_2594_, 0);
lean_inc(v_val_2605_);
v_a_2563_ = v_val_2605_;
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2564_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2565_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2566_ = l_Lean_addMacroScope(v_a_2563_, v___x_2565_, v_a_2561_);
v___x_2567_ = lean_box(0);
lean_inc_n(v___x_2559_, 4);
v___x_2568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2559_);
lean_ctor_set(v___x_2568_, 1, v___x_2564_);
lean_ctor_set(v___x_2568_, 2, v___x_2566_);
lean_ctor_set(v___x_2568_, 3, v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2559_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2572_ = l_Lean_Syntax_node1(v___x_2559_, v___x_2571_, v_stx_1751_);
v___x_2573_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2559_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_Syntax_node4(v___x_2559_, v___x_1763_, v___x_2568_, v___x_2570_, v___x_2572_, v___x_2574_);
v___x_2576_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2575_);
lean_ctor_set(v___x_2581_, 1, v_a_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v___x_2575_);
v_a_2586_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2576_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2576_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v___x_2559_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2606_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2560_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2560_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2614_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2557_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2557_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2623_; 
lean_dec(v_id_1750_);
v_val_2622_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2623_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2622_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v_pat_1756_ = v_a_2624_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_stx_1751_);
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
}
else
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = l_Lean_Syntax_getArg(v___x_2554_, v___x_2314_);
lean_dec(v___x_2554_);
v___x_2634_ = l_Lean_Syntax_matchesNull(v___x_2633_, v___x_2314_);
if (v___x_2634_ == 0)
{
lean_dec(v_stx_2474_);
lean_dec(v___x_2394_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = l_Lean_SourceInfo_fromRef(v_a_2636_, v___x_2634_);
lean_dec(v_a_2636_);
v___x_2638_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v_a_2641_; lean_object* v_quotContext_x3f_2672_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v_quotContext_x3f_2672_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2672_) == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v_a_2641_ = v_a_2674_;
goto v___jp_2640_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2639_);
lean_dec(v___x_2637_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
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
lean_object* v_val_2683_; 
v_val_2683_ = lean_ctor_get(v_quotContext_x3f_2672_, 0);
lean_inc(v_val_2683_);
v_a_2641_ = v_val_2683_;
goto v___jp_2640_;
}
v___jp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2642_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2644_ = l_Lean_addMacroScope(v_a_2641_, v___x_2643_, v_a_2639_);
v___x_2645_ = lean_box(0);
lean_inc_n(v___x_2637_, 4);
v___x_2646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2637_);
lean_ctor_set(v___x_2646_, 1, v___x_2642_);
lean_ctor_set(v___x_2646_, 2, v___x_2644_);
lean_ctor_set(v___x_2646_, 3, v___x_2645_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2637_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2650_ = l_Lean_Syntax_node1(v___x_2637_, v___x_2649_, v_stx_1751_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2637_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = l_Lean_Syntax_node4(v___x_2637_, v___x_1763_, v___x_2646_, v___x_2648_, v___x_2650_, v___x_2652_);
v___x_2654_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2663_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2653_);
lean_ctor_set(v___x_2659_, 1, v_a_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v___x_2653_);
v_a_2664_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2654_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2654_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v___x_2637_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2684_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2638_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2638_);
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
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2692_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2635_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2635_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v_val_2700_; lean_object* v___x_2701_; 
lean_dec(v_id_1750_);
v_val_2700_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2700_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2701_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2700_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v_pat_1756_ = v_a_2702_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_stx_1751_);
v_a_2703_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
else
{
v___y_2502_ = v_a_1752_;
v___y_2503_ = v_a_1753_;
goto v___jp_2501_;
}
}
}
else
{
lean_dec(v___x_2554_);
v___y_2502_ = v_a_1752_;
v___y_2503_ = v_a_1753_;
goto v___jp_2501_;
}
v___jp_2475_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_2481_ = lean_string_append(v___y_2479_, v___x_2480_);
lean_inc(v___y_2477_);
v___x_2482_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___y_2477_, v_stx_2474_, v_id_1750_, v___x_2481_, v___y_2476_, v___y_2478_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v_pat_1756_ = v_a_2483_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_stx_1751_);
v_a_2484_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2482_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2482_);
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
v___jp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__14));
v___x_2496_ = l_Lean_Syntax_isStrLit_x3f(v___x_2394_);
lean_dec(v___x_2394_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__18);
v___x_2498_ = l_panic___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__1(v___x_2497_);
v___y_2476_ = v___y_2493_;
v___y_2477_ = v___x_2495_;
v___y_2478_ = v___y_2494_;
v___y_2479_ = v___x_2498_;
goto v___jp_2475_;
}
else
{
lean_object* v_val_2499_; 
v_val_2499_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v___x_2496_, 1);
v___y_2476_ = v___y_2493_;
v___y_2477_ = v___x_2495_;
v___y_2478_ = v___y_2494_;
v___y_2479_ = v_val_2499_;
goto v___jp_2475_;
}
}
v___jp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2504_ = lean_unsigned_to_nat(5u);
v___x_2505_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_isNone(v___x_2505_);
if (v___x_2506_ == 0)
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Lean_Syntax_matchesNull(v___x_2505_, v___x_2500_);
if (v___x_2507_ == 0)
{
lean_dec(v_stx_2474_);
lean_dec(v___x_2394_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Elab_Command_getRef___redArg(v___y_2502_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = l_Lean_SourceInfo_fromRef(v_a_2509_, v___x_2507_);
lean_dec(v_a_2509_);
v___x_2511_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2502_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_quotContext_x3f_2512_; 
v_quotContext_x3f_2512_ = lean_ctor_get(v___y_2502_, 5);
if (lean_obj_tag(v_quotContext_x3f_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; 
v_a_2513_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2514_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v___y_2503_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_1801_ = v___y_2503_;
v___y_1802_ = v___y_2502_;
v___y_1803_ = v___x_2510_;
v___y_1804_ = v_a_2513_;
v_a_1805_ = v_a_2515_;
goto v___jp_1800_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2513_);
lean_dec(v___x_2510_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2516_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2514_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2514_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v_val_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2511_, 1);
v_val_2525_ = lean_ctor_get(v_quotContext_x3f_2512_, 0);
lean_inc(v_val_2525_);
v___y_1801_ = v___y_2503_;
v___y_1802_ = v___y_2502_;
v___y_1803_ = v___x_2510_;
v___y_1804_ = v_a_2524_;
v_a_1805_ = v_val_2525_;
goto v___jp_1800_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v___x_2510_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2526_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2511_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2511_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2534_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2508_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2508_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_val_2542_; lean_object* v___x_2543_; 
lean_dec(v_id_1750_);
v_val_2542_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2542_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2543_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2542_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v_pat_1756_ = v_a_2544_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_stx_1751_);
v_a_2545_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2543_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2543_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
else
{
lean_dec(v_id_x3f_1749_);
v___y_2493_ = v___y_2502_;
v___y_2494_ = v___y_2503_;
goto v___jp_2492_;
}
}
else
{
lean_dec(v___x_2505_);
lean_dec(v_id_x3f_1749_);
v___y_2493_ = v___y_2502_;
v___y_2494_ = v___y_2503_;
goto v___jp_2492_;
}
}
}
}
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2711_);
v___x_2713_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__20));
v___x_2714_ = l_Lean_Syntax_matchesIdent(v___x_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__22));
v___x_2716_ = l_Lean_Syntax_matchesIdent(v___x_2712_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__24));
v___x_2718_ = l_Lean_Syntax_matchesIdent(v___x_2712_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__26));
v___x_2720_ = l_Lean_Syntax_matchesIdent(v___x_2712_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__28));
v___x_2722_ = l_Lean_Syntax_matchesIdent(v___x_2712_, v___x_2721_);
lean_dec(v___x_2712_);
if (v___x_2722_ == 0)
{
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
v___x_2725_ = l_Lean_SourceInfo_fromRef(v_a_2724_, v___x_2722_);
lean_dec(v_a_2724_);
v___x_2726_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v_a_2729_; lean_object* v_quotContext_x3f_2760_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v_quotContext_x3f_2760_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2760_) == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v_a_2729_ = v_a_2762_;
goto v___jp_2728_;
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2727_);
lean_dec(v___x_2725_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2763_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2761_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2761_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_val_2771_; 
v_val_2771_ = lean_ctor_get(v_quotContext_x3f_2760_, 0);
lean_inc(v_val_2771_);
v_a_2729_ = v_val_2771_;
goto v___jp_2728_;
}
v___jp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2730_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2731_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2732_ = l_Lean_addMacroScope(v_a_2729_, v___x_2731_, v_a_2727_);
v___x_2733_ = lean_box(0);
lean_inc_n(v___x_2725_, 4);
v___x_2734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2725_);
lean_ctor_set(v___x_2734_, 1, v___x_2730_);
lean_ctor_set(v___x_2734_, 2, v___x_2732_);
lean_ctor_set(v___x_2734_, 3, v___x_2733_);
v___x_2735_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2725_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2738_ = l_Lean_Syntax_node1(v___x_2725_, v___x_2737_, v_stx_1751_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2725_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Lean_Syntax_node4(v___x_2725_, v___x_1763_, v___x_2734_, v___x_2736_, v___x_2738_, v___x_2740_);
v___x_2742_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2741_);
lean_ctor_set(v___x_2747_, 1, v_a_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v___x_2741_);
v_a_2752_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2742_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2742_);
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
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v___x_2725_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2772_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2726_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2726_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2780_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2723_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2723_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2789_; 
lean_dec(v_id_1750_);
v_val_2788_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2789_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2788_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v_pat_1756_ = v_a_2790_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_stx_1751_);
v_a_2791_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2789_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2789_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = lean_unsigned_to_nat(2u);
v___x_2801_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2800_);
lean_inc(v___x_2801_);
v___x_2802_ = l_Lean_Syntax_matchesNull(v___x_2801_, v___x_2799_);
if (v___x_2802_ == 0)
{
lean_dec(v___x_2801_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = l_Lean_SourceInfo_fromRef(v_a_2804_, v___x_2802_);
lean_dec(v_a_2804_);
v___x_2806_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_a_2809_; lean_object* v_quotContext_x3f_2840_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_quotContext_x3f_2840_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2840_) == 0)
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v_a_2809_ = v_a_2842_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2807_);
lean_dec(v___x_2805_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2843_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2841_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2841_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_val_2851_; 
v_val_2851_ = lean_ctor_get(v_quotContext_x3f_2840_, 0);
lean_inc(v_val_2851_);
v_a_2809_ = v_val_2851_;
goto v___jp_2808_;
}
v___jp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2810_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2811_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2812_ = l_Lean_addMacroScope(v_a_2809_, v___x_2811_, v_a_2807_);
v___x_2813_ = lean_box(0);
lean_inc_n(v___x_2805_, 4);
v___x_2814_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2805_);
lean_ctor_set(v___x_2814_, 1, v___x_2810_);
lean_ctor_set(v___x_2814_, 2, v___x_2812_);
lean_ctor_set(v___x_2814_, 3, v___x_2813_);
v___x_2815_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2805_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2818_ = l_Lean_Syntax_node1(v___x_2805_, v___x_2817_, v_stx_1751_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2805_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = l_Lean_Syntax_node4(v___x_2805_, v___x_1763_, v___x_2814_, v___x_2816_, v___x_2818_, v___x_2820_);
v___x_2822_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2831_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2821_);
lean_ctor_set(v___x_2827_, 1, v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v___x_2821_);
v_a_2832_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2822_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2822_);
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
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v___x_2805_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2852_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2806_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2806_);
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
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2860_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2803_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2803_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_val_2868_; lean_object* v___x_2869_; 
lean_dec(v_id_1750_);
v_val_2868_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_2869_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_2868_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v_pat_1756_ = v_a_2870_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_stx_1751_);
v_a_2871_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2869_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
else
{
lean_object* v_stx_2879_; lean_object* v___x_2880_; 
lean_dec(v_stx_1751_);
v_stx_2879_ = l_Lean_Syntax_getArg(v___x_2801_, v___x_2711_);
lean_dec(v___x_2801_);
v___x_2880_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_1749_, v_id_1750_, v_stx_2879_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v_fst_2882_; lean_object* v_snd_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2943_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v_fst_2882_ = lean_ctor_get(v_a_2881_, 0);
v_snd_2883_ = lean_ctor_get(v_a_2881_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_a_2881_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2885_ = v_a_2881_;
v_isShared_2886_ = v_isSharedCheck_2943_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_snd_2883_);
lean_inc(v_fst_2882_);
lean_dec(v_a_2881_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2943_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = l_Lean_SourceInfo_fromRef(v_a_2888_, v___x_2720_);
lean_dec(v_a_2888_);
v___x_2890_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2926_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2926_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2926_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_a_2896_; lean_object* v_quotContext_x3f_2914_; 
v_quotContext_x3f_2914_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2914_) == 0)
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v_a_2896_ = v_a_2916_;
goto v___jp_2895_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_del_object(v___x_2893_);
lean_dec(v_a_2891_);
lean_dec(v___x_2889_);
lean_del_object(v___x_2885_);
lean_dec(v_snd_2883_);
lean_dec(v_fst_2882_);
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
else
{
lean_object* v_val_2925_; 
v_val_2925_ = lean_ctor_get(v_quotContext_x3f_2914_, 0);
lean_inc(v_val_2925_);
v_a_2896_ = v_val_2925_;
goto v___jp_2895_;
}
v___jp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2897_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__29);
v___x_2898_ = l_Lean_addMacroScope(v_a_2896_, v___x_2721_, v_a_2891_);
v___x_2899_ = lean_box(0);
lean_inc_n(v___x_2889_, 4);
v___x_2900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2889_);
lean_ctor_set(v___x_2900_, 1, v___x_2897_);
lean_ctor_set(v___x_2900_, 2, v___x_2898_);
lean_ctor_set(v___x_2900_, 3, v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2889_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
v___x_2904_ = l_Lean_Syntax_node1(v___x_2889_, v___x_2903_, v_fst_2882_);
v___x_2905_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2889_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_Syntax_node4(v___x_2889_, v___x_1763_, v___x_2900_, v___x_2902_, v___x_2904_, v___x_2906_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v___x_2907_);
v___x_2909_ = v___x_2885_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_snd_2883_);
v___x_2909_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2909_);
v___x_2911_ = v___x_2893_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
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
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v___x_2889_);
lean_del_object(v___x_2885_);
lean_dec(v_snd_2883_);
lean_dec(v_fst_2882_);
v_a_2927_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2890_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2890_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_del_object(v___x_2885_);
lean_dec(v_snd_2883_);
lean_dec(v_fst_2882_);
v_a_2935_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2887_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2887_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
else
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
lean_dec(v___x_2712_);
v___x_2944_ = lean_unsigned_to_nat(1u);
v___x_2945_ = lean_unsigned_to_nat(2u);
v___x_2946_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_2945_);
lean_inc(v___x_2946_);
v___x_2947_ = l_Lean_Syntax_matchesNull(v___x_2946_, v___x_2944_);
if (v___x_2947_ == 0)
{
lean_dec(v___x_2946_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = l_Lean_SourceInfo_fromRef(v_a_2949_, v___x_2947_);
lean_dec(v_a_2949_);
v___x_2951_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v_a_2954_; lean_object* v_quotContext_x3f_2985_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v_quotContext_x3f_2985_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_2985_) == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v_a_2954_ = v_a_2987_;
goto v___jp_2953_;
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v_a_2952_);
lean_dec(v___x_2950_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2988_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2986_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2986_);
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
else
{
lean_object* v_val_2996_; 
v_val_2996_ = lean_ctor_get(v_quotContext_x3f_2985_, 0);
lean_inc(v_val_2996_);
v_a_2954_ = v_val_2996_;
goto v___jp_2953_;
}
v___jp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2955_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_2956_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_2957_ = l_Lean_addMacroScope(v_a_2954_, v___x_2956_, v_a_2952_);
v___x_2958_ = lean_box(0);
lean_inc_n(v___x_2950_, 4);
v___x_2959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2950_);
lean_ctor_set(v___x_2959_, 1, v___x_2955_);
lean_ctor_set(v___x_2959_, 2, v___x_2957_);
lean_ctor_set(v___x_2959_, 3, v___x_2958_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_2961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2950_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_2963_ = l_Lean_Syntax_node1(v___x_2950_, v___x_2962_, v_stx_1751_);
v___x_2964_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_2965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2950_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Lean_Syntax_node4(v___x_2950_, v___x_1763_, v___x_2959_, v___x_2961_, v___x_2963_, v___x_2965_);
v___x_2967_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2976_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2976_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2976_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2966_);
lean_ctor_set(v___x_2972_, 1, v_a_2968_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2972_);
v___x_2974_ = v___x_2970_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v___x_2966_);
v_a_2977_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2967_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2967_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v___x_2950_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_2997_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2951_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2951_);
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
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3005_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2948_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2948_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
lean_object* v_val_3013_; lean_object* v___x_3014_; 
lean_dec(v_id_1750_);
v_val_3013_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3013_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3014_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3013_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v_pat_1756_ = v_a_3015_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_stx_1751_);
v_a_3016_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3014_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3014_);
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
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3024_ = l_Lean_Syntax_getArg(v___x_2946_, v___x_2711_);
lean_dec(v___x_2946_);
v___x_3025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__4));
lean_inc(v___x_3024_);
v___x_3026_ = l_Lean_Syntax_isOfKind(v___x_3024_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_dec(v___x_3024_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3029_ = l_Lean_SourceInfo_fromRef(v_a_3028_, v___x_3026_);
lean_dec(v_a_3028_);
v___x_3030_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_a_3033_; lean_object* v_quotContext_x3f_3064_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v_quotContext_x3f_3064_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3064_) == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v_a_3033_ = v_a_3066_;
goto v___jp_3032_;
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_3031_);
lean_dec(v___x_3029_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3067_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3065_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3065_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_val_3075_; 
v_val_3075_ = lean_ctor_get(v_quotContext_x3f_3064_, 0);
lean_inc(v_val_3075_);
v_a_3033_ = v_val_3075_;
goto v___jp_3032_;
}
v___jp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3034_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3036_ = l_Lean_addMacroScope(v_a_3033_, v___x_3035_, v_a_3031_);
v___x_3037_ = lean_box(0);
lean_inc_n(v___x_3029_, 4);
v___x_3038_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3029_);
lean_ctor_set(v___x_3038_, 1, v___x_3034_);
lean_ctor_set(v___x_3038_, 2, v___x_3036_);
lean_ctor_set(v___x_3038_, 3, v___x_3037_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3029_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3042_ = l_Lean_Syntax_node1(v___x_3029_, v___x_3041_, v_stx_1751_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3029_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_Syntax_node4(v___x_3029_, v___x_1763_, v___x_3038_, v___x_3040_, v___x_3042_, v___x_3044_);
v___x_3046_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3055_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3055_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3055_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3045_);
lean_ctor_set(v___x_3051_, 1, v_a_3047_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3051_);
v___x_3053_ = v___x_3049_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___x_3045_);
v_a_3056_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3046_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3046_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v___x_3029_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3076_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3030_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3030_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3084_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3027_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3027_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_val_3092_; lean_object* v___x_3093_; 
lean_dec(v_id_1750_);
v_val_3092_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3093_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3092_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v_pat_1756_ = v_a_3094_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_stx_1751_);
v_a_3095_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3093_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3093_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3103_ = l_Lean_Syntax_getArg(v___x_3024_, v___x_2711_);
v___x_3104_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__31));
v___x_3105_ = l_Lean_Syntax_matchesIdent(v___x_3103_, v___x_3104_);
lean_dec(v___x_3103_);
if (v___x_3105_ == 0)
{
lean_dec(v___x_3024_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_SourceInfo_fromRef(v_a_3107_, v___x_3105_);
lean_dec(v_a_3107_);
v___x_3109_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_a_3112_; lean_object* v_quotContext_x3f_3143_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v_quotContext_x3f_3143_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3143_) == 0)
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v_a_3112_ = v_a_3145_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_3110_);
lean_dec(v___x_3108_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3146_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3144_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3144_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_val_3154_; 
v_val_3154_ = lean_ctor_get(v_quotContext_x3f_3143_, 0);
lean_inc(v_val_3154_);
v_a_3112_ = v_val_3154_;
goto v___jp_3111_;
}
v___jp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3113_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3114_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3115_ = l_Lean_addMacroScope(v_a_3112_, v___x_3114_, v_a_3110_);
v___x_3116_ = lean_box(0);
lean_inc_n(v___x_3108_, 4);
v___x_3117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3108_);
lean_ctor_set(v___x_3117_, 1, v___x_3113_);
lean_ctor_set(v___x_3117_, 2, v___x_3115_);
lean_ctor_set(v___x_3117_, 3, v___x_3116_);
v___x_3118_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3108_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3121_ = l_Lean_Syntax_node1(v___x_3108_, v___x_3120_, v_stx_1751_);
v___x_3122_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3108_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_Syntax_node4(v___x_3108_, v___x_1763_, v___x_3117_, v___x_3119_, v___x_3121_, v___x_3123_);
v___x_3125_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3124_);
lean_ctor_set(v___x_3130_, 1, v_a_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___x_3124_);
v_a_3135_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3125_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3125_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v___x_3108_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3155_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3109_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3109_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3163_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3106_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3106_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_val_3171_; lean_object* v___x_3172_; 
lean_dec(v_id_1750_);
v_val_3171_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3172_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3171_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v_pat_1756_ = v_a_3173_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_stx_1751_);
v_a_3174_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3172_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3172_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
else
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = l_Lean_Syntax_getArg(v___x_3024_, v___x_2944_);
lean_dec(v___x_3024_);
v___x_3183_ = l_Lean_Syntax_matchesNull(v___x_3182_, v___x_2711_);
if (v___x_3183_ == 0)
{
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = l_Lean_SourceInfo_fromRef(v_a_3185_, v___x_3183_);
lean_dec(v_a_3185_);
v___x_3187_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v_a_3190_; lean_object* v_quotContext_x3f_3221_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v_quotContext_x3f_3221_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3221_) == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v_a_3190_ = v_a_3223_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v_a_3188_);
lean_dec(v___x_3186_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3224_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3222_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3222_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_val_3232_; 
v_val_3232_ = lean_ctor_get(v_quotContext_x3f_3221_, 0);
lean_inc(v_val_3232_);
v_a_3190_ = v_val_3232_;
goto v___jp_3189_;
}
v___jp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3191_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3192_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3193_ = l_Lean_addMacroScope(v_a_3190_, v___x_3192_, v_a_3188_);
v___x_3194_ = lean_box(0);
lean_inc_n(v___x_3186_, 4);
v___x_3195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3186_);
lean_ctor_set(v___x_3195_, 1, v___x_3191_);
lean_ctor_set(v___x_3195_, 2, v___x_3193_);
lean_ctor_set(v___x_3195_, 3, v___x_3194_);
v___x_3196_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3186_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3199_ = l_Lean_Syntax_node1(v___x_3186_, v___x_3198_, v_stx_1751_);
v___x_3200_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3186_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = l_Lean_Syntax_node4(v___x_3186_, v___x_1763_, v___x_3195_, v___x_3197_, v___x_3199_, v___x_3201_);
v___x_3203_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3212_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3212_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3212_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3202_);
lean_ctor_set(v___x_3208_, 1, v_a_3204_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3208_);
v___x_3210_ = v___x_3206_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v___x_3202_);
v_a_3213_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3203_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3203_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec(v___x_3186_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3233_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3187_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3187_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3241_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3184_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3184_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_val_3249_; lean_object* v___x_3250_; 
lean_dec(v_id_1750_);
v_val_3249_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3249_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3250_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3249_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v_pat_1756_ = v_a_3251_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_stx_1751_);
v_a_3252_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3250_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3250_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v_id_x3f_1749_);
v___x_3260_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__33));
v___x_3261_ = lean_box(0);
v___x_3262_ = l_Lean_Syntax_mkAntiquotNode(v___x_3260_, v_id_1750_, v___x_2711_, v___x_3261_, v___x_2718_);
v_pat_1756_ = v___x_3262_;
goto v___jp_1755_;
}
}
}
}
}
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
lean_dec(v___x_2712_);
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_unsigned_to_nat(2u);
v___x_3265_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_3264_);
lean_inc(v___x_3265_);
v___x_3266_ = l_Lean_Syntax_matchesNull(v___x_3265_, v___x_3263_);
if (v___x_3266_ == 0)
{
lean_dec(v___x_3265_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 1);
v___x_3269_ = l_Lean_SourceInfo_fromRef(v_a_3268_, v___x_3266_);
lean_dec(v_a_3268_);
v___x_3270_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v_a_3273_; lean_object* v_quotContext_x3f_3304_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v_quotContext_x3f_3304_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3304_) == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v_a_3273_ = v_a_3306_;
goto v___jp_3272_;
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_a_3271_);
lean_dec(v___x_3269_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3307_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3305_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3305_);
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
else
{
lean_object* v_val_3315_; 
v_val_3315_ = lean_ctor_get(v_quotContext_x3f_3304_, 0);
lean_inc(v_val_3315_);
v_a_3273_ = v_val_3315_;
goto v___jp_3272_;
}
v___jp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3274_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3275_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3276_ = l_Lean_addMacroScope(v_a_3273_, v___x_3275_, v_a_3271_);
v___x_3277_ = lean_box(0);
lean_inc_n(v___x_3269_, 4);
v___x_3278_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3269_);
lean_ctor_set(v___x_3278_, 1, v___x_3274_);
lean_ctor_set(v___x_3278_, 2, v___x_3276_);
lean_ctor_set(v___x_3278_, 3, v___x_3277_);
v___x_3279_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3269_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3282_ = l_Lean_Syntax_node1(v___x_3269_, v___x_3281_, v_stx_1751_);
v___x_3283_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3269_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_Syntax_node4(v___x_3269_, v___x_1763_, v___x_3278_, v___x_3280_, v___x_3282_, v___x_3284_);
v___x_3286_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3295_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3285_);
lean_ctor_set(v___x_3291_, 1, v_a_3287_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3291_);
v___x_3293_ = v___x_3289_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v___x_3285_);
v_a_3296_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3286_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3286_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec(v___x_3269_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3316_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3270_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3270_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3324_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3267_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3267_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3333_; 
lean_dec(v_id_1750_);
v_val_3332_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3333_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3332_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v_pat_1756_ = v_a_3334_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_stx_1751_);
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
else
{
lean_object* v_stx_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec(v_id_x3f_1749_);
v_stx_3343_ = l_Lean_Syntax_getArg(v___x_3265_, v___x_2711_);
lean_dec(v___x_3265_);
v___x_3344_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3345_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2715_, v_stx_3343_, v_id_1750_, v___x_3344_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v_pat_1756_ = v_a_3346_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec(v_stx_1751_);
v_a_3347_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3345_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3345_);
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
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
lean_dec(v___x_2712_);
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_unsigned_to_nat(2u);
v___x_3357_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_3356_);
lean_inc(v___x_3357_);
v___x_3358_ = l_Lean_Syntax_matchesNull(v___x_3357_, v___x_3355_);
if (v___x_3358_ == 0)
{
lean_dec(v___x_3357_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = l_Lean_SourceInfo_fromRef(v_a_3360_, v___x_3358_);
lean_dec(v_a_3360_);
v___x_3362_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v_a_3365_; lean_object* v_quotContext_x3f_3396_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v_quotContext_x3f_3396_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3396_) == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v_a_3365_ = v_a_3398_;
goto v___jp_3364_;
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3363_);
lean_dec(v___x_3361_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3399_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_val_3407_; 
v_val_3407_ = lean_ctor_get(v_quotContext_x3f_3396_, 0);
lean_inc(v_val_3407_);
v_a_3365_ = v_val_3407_;
goto v___jp_3364_;
}
v___jp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3366_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3368_ = l_Lean_addMacroScope(v_a_3365_, v___x_3367_, v_a_3363_);
v___x_3369_ = lean_box(0);
lean_inc_n(v___x_3361_, 4);
v___x_3370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3361_);
lean_ctor_set(v___x_3370_, 1, v___x_3366_);
lean_ctor_set(v___x_3370_, 2, v___x_3368_);
lean_ctor_set(v___x_3370_, 3, v___x_3369_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3361_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3374_ = l_Lean_Syntax_node1(v___x_3361_, v___x_3373_, v_stx_1751_);
v___x_3375_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3361_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = l_Lean_Syntax_node4(v___x_3361_, v___x_1763_, v___x_3370_, v___x_3372_, v___x_3374_, v___x_3376_);
v___x_3378_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3387_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3387_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3387_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3377_);
lean_ctor_set(v___x_3383_, 1, v_a_3379_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3383_);
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v___x_3377_);
v_a_3388_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3378_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3378_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v___x_3361_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3408_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3362_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3362_);
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
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3416_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3359_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3359_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_val_3424_; lean_object* v___x_3425_; 
lean_dec(v_id_1750_);
v_val_3424_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3424_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3425_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3424_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v_pat_1756_ = v_a_3426_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_stx_1751_);
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
else
{
lean_object* v_stx_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec(v_id_x3f_1749_);
v_stx_3435_ = l_Lean_Syntax_getArg(v___x_3357_, v___x_2711_);
lean_dec(v___x_3357_);
v___x_3436_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__13));
v___x_3437_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2715_, v_stx_3435_, v_id_1750_, v___x_3436_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v_pat_1756_ = v_a_3438_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_stx_1751_);
v_a_3439_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3437_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3437_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
lean_dec(v___x_2712_);
v___x_3447_ = lean_unsigned_to_nat(1u);
v___x_3448_ = lean_unsigned_to_nat(2u);
v___x_3449_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_3448_);
lean_inc(v___x_3449_);
v___x_3450_ = l_Lean_Syntax_matchesNull(v___x_3449_, v___x_3447_);
if (v___x_3450_ == 0)
{
lean_dec(v___x_3449_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = l_Lean_SourceInfo_fromRef(v_a_3452_, v___x_3450_);
lean_dec(v_a_3452_);
v___x_3454_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v_a_3457_; lean_object* v_quotContext_x3f_3488_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v_quotContext_x3f_3488_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3488_) == 0)
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v_a_3457_ = v_a_3490_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_a_3455_);
lean_dec(v___x_3453_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
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
else
{
lean_object* v_val_3499_; 
v_val_3499_ = lean_ctor_get(v_quotContext_x3f_3488_, 0);
lean_inc(v_val_3499_);
v_a_3457_ = v_val_3499_;
goto v___jp_3456_;
}
v___jp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3458_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3459_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3460_ = l_Lean_addMacroScope(v_a_3457_, v___x_3459_, v_a_3455_);
v___x_3461_ = lean_box(0);
lean_inc_n(v___x_3453_, 4);
v___x_3462_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3453_);
lean_ctor_set(v___x_3462_, 1, v___x_3458_);
lean_ctor_set(v___x_3462_, 2, v___x_3460_);
lean_ctor_set(v___x_3462_, 3, v___x_3461_);
v___x_3463_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3453_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3466_ = l_Lean_Syntax_node1(v___x_3453_, v___x_3465_, v_stx_1751_);
v___x_3467_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3453_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_Syntax_node4(v___x_3453_, v___x_1763_, v___x_3462_, v___x_3464_, v___x_3466_, v___x_3468_);
v___x_3470_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3479_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3469_);
lean_ctor_set(v___x_3475_, 1, v_a_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v___x_3469_);
v_a_3480_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3470_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3470_);
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
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec(v___x_3453_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3500_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3454_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3454_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3508_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3451_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3451_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_val_3516_; lean_object* v___x_3517_; 
lean_dec(v_id_1750_);
v_val_3516_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3516_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3517_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3516_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v_pat_1756_ = v_a_3518_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v_stx_1751_);
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
else
{
lean_object* v_stx_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_dec(v_id_x3f_1749_);
v_stx_3527_ = l_Lean_Syntax_getArg(v___x_3449_, v___x_2711_);
lean_dec(v___x_3449_);
v___x_3528_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__34));
v___x_3529_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat(v___x_2713_, v_stx_3527_, v_id_1750_, v___x_3528_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v_pat_1756_ = v_a_3530_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v_stx_1751_);
v_a_3531_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3529_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
v___jp_1764_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1770_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1771_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1772_ = l_Lean_addMacroScope(v_a_1769_, v___x_1771_, v___y_1767_);
v___x_1773_ = lean_box(0);
lean_inc_n(v___y_1765_, 4);
v___x_1774_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1774_, 0, v___y_1765_);
lean_ctor_set(v___x_1774_, 1, v___x_1770_);
lean_ctor_set(v___x_1774_, 2, v___x_1772_);
lean_ctor_set(v___x_1774_, 3, v___x_1773_);
v___x_1775_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___y_1765_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_1778_ = l_Lean_Syntax_node1(v___y_1765_, v___x_1777_, v_stx_1751_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___y_1765_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node4(v___y_1765_, v___x_1763_, v___x_1774_, v___x_1776_, v___x_1778_, v___x_1780_);
v___x_1782_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v___y_1768_, v___y_1766_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1781_);
lean_ctor_set(v___x_1787_, 1, v_a_1783_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1787_);
v___x_1789_ = v___x_1785_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v___x_1781_);
v_a_1792_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1782_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1782_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
v___jp_1800_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_1807_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_1808_ = l_Lean_addMacroScope(v_a_1805_, v___x_1807_, v___y_1804_);
v___x_1809_ = lean_box(0);
lean_inc_n(v___y_1803_, 4);
v___x_1810_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1810_, 0, v___y_1803_);
lean_ctor_set(v___x_1810_, 1, v___x_1806_);
lean_ctor_set(v___x_1810_, 2, v___x_1808_);
lean_ctor_set(v___x_1810_, 3, v___x_1809_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_1812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___y_1803_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_1814_ = l_Lean_Syntax_node1(v___y_1803_, v___x_1813_, v_stx_1751_);
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_1816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1803_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_Syntax_node4(v___y_1803_, v___x_1763_, v___x_1810_, v___x_1812_, v___x_1814_, v___x_1816_);
v___x_1818_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v___y_1802_, v___y_1801_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1817_);
lean_ctor_set(v___x_1823_, 1, v_a_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v___x_1817_);
v_a_1828_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1818_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1818_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_3539_);
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3540_);
v___x_3542_ = l_Lean_Syntax_isOfKind(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_dec(v___x_3540_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Lean_SourceInfo_fromRef(v_a_3544_, v___x_1760_);
lean_dec(v_a_3544_);
v___x_3546_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v_a_3549_; lean_object* v_quotContext_x3f_3581_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v_quotContext_x3f_3581_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3581_) == 0)
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v_a_3549_ = v_a_3583_;
goto v___jp_3548_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_a_3547_);
lean_dec(v___x_3545_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
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
v_val_3592_ = lean_ctor_get(v_quotContext_x3f_3581_, 0);
lean_inc(v_val_3592_);
v_a_3549_ = v_val_3592_;
goto v___jp_3548_;
}
v___jp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3551_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3553_ = l_Lean_addMacroScope(v_a_3549_, v___x_3552_, v_a_3547_);
v___x_3554_ = lean_box(0);
lean_inc_n(v___x_3545_, 4);
v___x_3555_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3545_);
lean_ctor_set(v___x_3555_, 1, v___x_3551_);
lean_ctor_set(v___x_3555_, 2, v___x_3553_);
lean_ctor_set(v___x_3555_, 3, v___x_3554_);
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3545_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3559_ = l_Lean_Syntax_node1(v___x_3545_, v___x_3558_, v_stx_1751_);
v___x_3560_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3545_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = l_Lean_Syntax_node4(v___x_3545_, v___x_3550_, v___x_3555_, v___x_3557_, v___x_3559_, v___x_3561_);
v___x_3563_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3572_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3562_);
lean_ctor_set(v___x_3568_, 1, v_a_3564_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3568_);
v___x_3570_ = v___x_3566_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v___x_3562_);
v_a_3573_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3563_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3563_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec(v___x_3545_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
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
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3601_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3543_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3543_);
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
lean_dec(v_id_1750_);
v_val_3609_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3610_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3609_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v_pat_1756_ = v_a_3611_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_stx_1751_);
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
lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_dec(v_id_x3f_1749_);
v___x_3620_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3620_, 0, v___x_3540_);
v___x_3621_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3620_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3623_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3624_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3625_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3626_ = lean_unsigned_to_nat(4u);
v___x_3627_ = lean_mk_empty_array_with_capacity(v___x_3626_);
v___x_3628_ = lean_array_push(v___x_3627_, v_a_3622_);
v___x_3629_ = lean_array_push(v___x_3628_, v___x_3624_);
v___x_3630_ = lean_array_push(v___x_3629_, v___x_3625_);
v___x_3631_ = lean_array_push(v___x_3630_, v_id_1750_);
v___x_3632_ = lean_box(2);
v___x_3633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___x_3623_);
lean_ctor_set(v___x_3633_, 2, v___x_3631_);
v_pat_1756_ = v___x_3633_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3634_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3621_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3621_);
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
}
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3642_ = lean_unsigned_to_nat(0u);
v___x_3643_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_3642_);
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___closed__5));
lean_inc(v___x_3643_);
v___x_3645_ = l_Lean_Syntax_isOfKind(v___x_3643_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_dec(v___x_3643_);
if (lean_obj_tag(v_id_x3f_1749_) == 0)
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Elab_Command_getRef___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = l_Lean_SourceInfo_fromRef(v_a_3647_, v___x_3645_);
lean_dec(v_a_3647_);
v___x_3649_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1752_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v_a_3652_; lean_object* v_quotContext_x3f_3684_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v_quotContext_x3f_3684_ = lean_ctor_get(v_a_1752_, 5);
if (lean_obj_tag(v_quotContext_x3f_3684_) == 0)
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_1753_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v_a_3652_ = v_a_3686_;
goto v___jp_3651_;
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_a_3650_);
lean_dec(v___x_3648_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
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
else
{
lean_object* v_val_3695_; 
v_val_3695_ = lean_ctor_get(v_quotContext_x3f_3684_, 0);
lean_inc(v_val_3695_);
v_a_3652_ = v_val_3695_;
goto v___jp_3651_;
}
v___jp_3651_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode_spec__4___closed__6));
v___x_3654_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__5);
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__6));
v___x_3656_ = l_Lean_addMacroScope(v_a_3652_, v___x_3655_, v_a_3650_);
v___x_3657_ = lean_box(0);
lean_inc_n(v___x_3648_, 4);
v___x_3658_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3648_);
lean_ctor_set(v___x_3658_, 1, v___x_3654_);
lean_ctor_set(v___x_3658_, 2, v___x_3656_);
lean_ctor_set(v___x_3658_, 3, v___x_3657_);
v___x_3659_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__7));
v___x_3660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3648_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSplicePat___closed__1));
lean_inc(v_stx_1751_);
v___x_3662_ = l_Lean_Syntax_node1(v___x_3648_, v___x_3661_, v_stx_1751_);
v___x_3663_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__8));
v___x_3664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3648_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_Syntax_node4(v___x_3648_, v___x_3653_, v___x_3658_, v___x_3660_, v___x_3662_, v___x_3664_);
v___x_3666_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_id_1750_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3675_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3665_);
lean_ctor_set(v___x_3671_, 1, v_a_3667_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3671_);
v___x_3673_ = v___x_3669_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec(v___x_3665_);
v_a_3676_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3666_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3666_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v___x_3648_);
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3696_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3649_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3649_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3704_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3646_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3646_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_val_3712_; lean_object* v___x_3713_; 
lean_dec(v_id_1750_);
v_val_3712_ = lean_ctor_get(v_id_x3f_1749_, 0);
lean_inc(v_val_3712_);
lean_dec_ref_known(v_id_x3f_1749_, 1);
lean_inc(v_stx_1751_);
v___x_3713_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode(v_stx_1751_, v_val_3712_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v_pat_1756_ = v_a_3714_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v_stx_1751_);
v_a_3715_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3713_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3713_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec(v_id_x3f_1749_);
v___x_3723_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_strLitToPattern___boxed), 3, 1);
lean_closure_set(v___x_3723_, 0, v___x_3643_);
v___x_3724_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v___x_3723_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__36));
v___x_3727_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__38);
v___x_3728_ = lean_obj_once(&l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40, &l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40_once, _init_l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___closed__40);
v___x_3729_ = lean_unsigned_to_nat(4u);
v___x_3730_ = lean_mk_empty_array_with_capacity(v___x_3729_);
v___x_3731_ = lean_array_push(v___x_3730_, v_a_3725_);
v___x_3732_ = lean_array_push(v___x_3731_, v___x_3727_);
v___x_3733_ = lean_array_push(v___x_3732_, v___x_3728_);
v___x_3734_ = lean_array_push(v___x_3733_, v_id_1750_);
v___x_3735_ = lean_box(2);
v___x_3736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___x_3726_);
lean_ctor_set(v___x_3736_, 2, v___x_3734_);
v_pat_1756_ = v___x_3736_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_stx_1751_);
lean_dec(v_id_1750_);
v_a_3737_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3724_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3724_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
v___jp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_stx_1751_);
lean_ctor_set(v___x_1757_, 1, v_pat_1756_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat___boxed(lean_object* v_id_x3f_3745_, lean_object* v_id_3746_, lean_object* v_stx_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v_id_x3f_3745_, v_id_3746_, v_stx_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(lean_object* v_00_u03b1_3752_, lean_object* v_x_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___redArg(v_x_3753_, v___y_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3757_, lean_object* v_x_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__3(v_00_u03b1_3757_, v_x_3758_, v___y_3759_, v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec_ref(v_x_3758_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(lean_object* v_00_u03b1_3762_, lean_object* v_ref_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___redArg(v_ref_3763_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8___boxed(lean_object* v_00_u03b1_3768_, lean_object* v_ref_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__8(v_00_u03b1_3768_, v_ref_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(lean_object* v_00_u03b1_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___boxed(lean_object* v_00_u03b1_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9(v_00_u03b1_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(lean_object* v_00_u03b1_3784_, lean_object* v_x_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___redArg(v_x_3785_, v___y_3786_, v___y_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2___boxed(lean_object* v_00_u03b1_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2(v_00_u03b1_3790_, v_x_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(lean_object* v_as_3796_, lean_object* v_as_x27_3797_, lean_object* v_b_3798_, lean_object* v_a_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___redArg(v_as_x27_3797_, v_b_3798_, v___y_3800_, v___y_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5___boxed(lean_object* v_as_3804_, lean_object* v_as_x27_3805_, lean_object* v_b_3806_, lean_object* v_a_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__5(v_as_3804_, v_as_x27_3805_, v_b_3806_, v_a_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v_as_x27_3805_);
lean_dec(v_as_3804_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(lean_object* v_00_u03b1_3812_, lean_object* v_ref_3813_, lean_object* v_msg_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___redArg(v_ref_3813_, v_msg_3814_, v___y_3815_, v___y_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7___boxed(lean_object* v_00_u03b1_3819_, lean_object* v_ref_3820_, lean_object* v_msg_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__7(v_00_u03b1_3819_, v_ref_3820_, v_msg_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v_ref_3820_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3826_, lean_object* v_m_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___redArg(v_m_3827_, v_a_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3830_, lean_object* v_m_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7(v_00_u03b2_3830_, v_m_3831_, v_a_3832_);
lean_dec(v_a_3832_);
lean_dec_ref(v_m_3831_);
return v_res_3833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
uint8_t v___x_3837_; 
v___x_3837_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___redArg(v_x_3835_, v_x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3838_, lean_object* v_x_3839_, lean_object* v_x_3840_){
_start:
{
uint8_t v_res_3841_; lean_object* v_r_3842_; 
v_res_3841_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8(v_00_u03b2_3838_, v_x_3839_, v_x_3840_);
lean_dec_ref(v_x_3840_);
lean_dec_ref(v_x_3839_);
v_r_3842_ = lean_box(v_res_3841_);
return v_r_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3843_, lean_object* v_a_3844_, lean_object* v_x_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___redArg(v_a_3844_, v_x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3847_, lean_object* v_a_3848_, lean_object* v_x_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_3847_, v_a_3848_, v_x_3849_);
lean_dec(v_x_3849_);
lean_dec(v_a_3848_);
return v_res_3850_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_3851_, lean_object* v_x_3852_, size_t v_x_3853_, lean_object* v_x_3854_){
_start:
{
uint8_t v___x_3855_; 
v___x_3855_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___redArg(v_x_3852_, v_x_3853_, v_x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3856_, lean_object* v_x_3857_, lean_object* v_x_3858_, lean_object* v_x_3859_){
_start:
{
size_t v_x_48345__boxed_3860_; uint8_t v_res_3861_; lean_object* v_r_3862_; 
v_x_48345__boxed_3860_ = lean_unbox_usize(v_x_3858_);
lean_dec(v_x_3858_);
v_res_3861_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12(v_00_u03b2_3856_, v_x_3857_, v_x_48345__boxed_3860_, v_x_3859_);
lean_dec_ref(v_x_3859_);
lean_dec_ref(v_x_3857_);
v_r_3862_ = lean_box(v_res_3861_);
return v_r_3862_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_3863_, lean_object* v_keys_3864_, lean_object* v_vals_3865_, lean_object* v_heq_3866_, lean_object* v_i_3867_, lean_object* v_k_3868_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___redArg(v_keys_3864_, v_i_3867_, v_k_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3870_, lean_object* v_keys_3871_, lean_object* v_vals_3872_, lean_object* v_heq_3873_, lean_object* v_i_3874_, lean_object* v_k_3875_){
_start:
{
uint8_t v_res_3876_; lean_object* v_r_3877_; 
v_res_3876_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__4_spec__5_spec__8_spec__12_spec__15(v_00_u03b2_3870_, v_keys_3871_, v_vals_3872_, v_heq_3873_, v_i_3874_, v_k_3875_);
lean_dec_ref(v_k_3875_);
lean_dec_ref(v_vals_3872_);
lean_dec_ref(v_keys_3871_);
v_r_3877_ = lean_box(v_res_3876_);
return v_r_3877_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_expandMacroArg___lam__0(lean_object* v_x_3884_){
_start:
{
lean_object* v___x_3885_; uint8_t v___x_3886_; 
v___x_3885_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___lam__0___closed__1));
v___x_3886_ = lean_name_eq(v_x_3884_, v___x_3885_);
if (v___x_3886_ == 0)
{
uint8_t v___x_3887_; 
v___x_3887_ = 1;
return v___x_3887_;
}
else
{
uint8_t v___x_3888_; 
v___x_3888_ = 0;
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___lam__0___boxed(lean_object* v_x_3889_){
_start:
{
uint8_t v_res_3890_; lean_object* v_r_3891_; 
v_res_3890_ = l_Lean_Elab_Command_expandMacroArg___lam__0(v_x_3889_);
lean_dec(v_x_3889_);
v_r_3891_ = lean_box(v_res_3890_);
return v_r_3891_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMacroArg___closed__5(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__4));
v___x_3902_ = l_String_toRawSubstring_x27(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object* v_stx_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v___f_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___f_3909_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__0));
v___x_3910_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMacrosReportingDeprecated___boxed), 9, 2);
lean_closure_set(v___x_3910_, 0, v_stx_3905_);
lean_closure_set(v___x_3910_, 1, v___f_3909_);
v___x_3911_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_3910_, v_a_3906_, v_a_3907_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc_n(v_a_3912_, 2);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__3));
v___x_3914_ = l_Lean_Syntax_isOfKind(v_a_3912_, v___x_3913_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_a_3912_);
v___x_3915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = l_Lean_Syntax_getArg(v_a_3912_, v___x_3924_);
v___x_3926_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3925_);
v___x_3927_ = l_Lean_Syntax_matchesNull(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
uint8_t v___x_3928_; 
v___x_3928_ = l_Lean_Syntax_matchesNull(v___x_3925_, v___x_3924_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v_a_3912_);
v___x_3929_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = l_Lean_Syntax_getArg(v_a_3912_, v___x_3938_);
lean_dec(v_a_3912_);
v___x_3940_ = l_Lean_Elab_Command_getRef___redArg(v_a_3906_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
v___x_3942_ = l_Lean_SourceInfo_fromRef(v_a_3941_, v___x_3927_);
lean_dec(v_a_3941_);
v___x_3943_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3906_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_a_3946_; lean_object* v_quotContext_x3f_3954_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_quotContext_x3f_3954_ = lean_ctor_get(v_a_3906_, 5);
if (lean_obj_tag(v_quotContext_x3f_3954_) == 0)
{
lean_object* v___x_3955_; lean_object* v_a_3956_; 
v___x_3955_ = l_Lean_getMainModule___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__0___redArg(v_a_3907_);
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref(v___x_3955_);
v_a_3946_ = v_a_3956_;
goto v___jp_3945_;
}
else
{
lean_object* v_val_3957_; 
v_val_3957_ = lean_ctor_get(v_quotContext_x3f_3954_, 0);
lean_inc(v_val_3957_);
v_a_3946_ = v_val_3957_;
goto v___jp_3945_;
}
v___jp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3947_ = lean_obj_once(&l_Lean_Elab_Command_expandMacroArg___closed__5, &l_Lean_Elab_Command_expandMacroArg___closed__5_once, _init_l_Lean_Elab_Command_expandMacroArg___closed__5);
v___x_3948_ = ((lean_object*)(l_Lean_Elab_Command_expandMacroArg___closed__6));
v___x_3949_ = l_Lean_addMacroScope(v_a_3946_, v___x_3948_, v_a_3944_);
v___x_3950_ = lean_box(0);
v___x_3951_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3942_);
lean_ctor_set(v___x_3951_, 1, v___x_3947_);
lean_ctor_set(v___x_3951_, 2, v___x_3949_);
lean_ctor_set(v___x_3951_, 3, v___x_3950_);
v___x_3952_ = lean_box(0);
v___x_3953_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3952_, v___x_3951_, v___x_3939_, v_a_3906_, v_a_3907_);
return v___x_3953_;
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v___x_3942_);
lean_dec(v___x_3939_);
v_a_3958_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3943_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3943_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v___x_3939_);
v_a_3966_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3940_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3940_);
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
}
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3974_ = l_Lean_Syntax_getArg(v___x_3925_, v___x_3924_);
lean_dec(v___x_3925_);
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkAntiquotNode___lam__0___closed__1));
lean_inc(v___x_3974_);
v___x_3976_ = l_Lean_Syntax_isOfKind(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v___x_3974_);
lean_dec(v_a_3912_);
v___x_3977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat_spec__2_spec__9___redArg();
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
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
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = l_Lean_Syntax_getArg(v_a_3912_, v___x_3986_);
lean_dec(v_a_3912_);
lean_inc(v___x_3974_);
v___x_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3974_);
v___x_3989_ = l___private_Lean_Elab_MacroArgUtil_0__Lean_Elab_Command_expandMacroArg_mkSyntaxAndPat(v___x_3988_, v___x_3974_, v___x_3987_, v_a_3906_, v_a_3907_);
return v___x_3989_;
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v_a_3990_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3911_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3911_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMacroArg___boxed(lean_object* v_stx_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_Elab_Command_expandMacroArg(v_stx_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
return v_res_4002_;
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
