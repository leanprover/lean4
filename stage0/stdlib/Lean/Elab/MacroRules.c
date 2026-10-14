// Lean compiler output
// Module: Lean.Elab.MacroRules
// Imports: public import Lean.Elab.Syntax public import Lean.Elab.AuxDef
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "invalid macro_rules alternative, expected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "invalid macro_rules alternative, unexpected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "macroRules"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__4;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 217, 176, 227, 245, 86, 100, 50)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value),LEAN_SCALAR_PTR_LITERAL(153, 13, 84, 30, 172, 208, 133, 203)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "throw"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value),LEAN_SCALAR_PTR_LITERAL(60, 81, 80, 209, 187, 239, 255, 113)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadExcept"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 61, 69, 62, 207, 229, 53)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Macro.Exception.unsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Exception"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value;
static const lean_array_object l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "macro_rules"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 80, 75, 5, 165, 87, 197, 1)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_elabMacroRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabMacroRules___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_elabMacroRules___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabMacroRules"};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 95, 207, 180, 64, 53, 80, 160)}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object* v_00_u03b1_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(v_00_u03b1_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_env_22_; lean_object* v___x_23_; lean_object* v_mainModule_24_; lean_object* v___x_25_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = l_Lean_Environment_header(v_env_22_);
lean_dec_ref(v_env_22_);
v_mainModule_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_mainModule_24_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v_mainModule_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg___boxed(lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_26_);
lean_dec(v___y_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___boxed(lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_36_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_37_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_41_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
lean_ctor_set(v___x_43_, 2, v___x_42_);
lean_ctor_set(v___x_43_, 3, v___x_42_);
lean_ctor_set(v___x_43_, 4, v___x_41_);
lean_ctor_set(v___x_43_, 5, v___x_41_);
lean_ctor_set(v___x_43_, 6, v___x_41_);
lean_ctor_set(v___x_43_, 7, v___x_41_);
lean_ctor_set(v___x_43_, 8, v___x_41_);
lean_ctor_set(v___x_43_, 9, v___x_41_);
lean_ctor_set(v___x_43_, 10, v___x_41_);
lean_ctor_set(v___x_43_, 11, v___x_40_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(32u);
v___x_45_ = lean_mk_empty_array_with_capacity(v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_47_ = ((size_t)5ULL);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_unsigned_to_nat(32u);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_49_);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_52_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_48_);
lean_ctor_set(v___x_52_, 3, v___x_48_);
lean_ctor_set_usize(v___x_52_, 4, v___x_47_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_box(1);
v___x_54_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_55_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_env_61_; uint8_t v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_scopes_66_; lean_object* v___x_67_; lean_object* v_opts_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_60_ = lean_st_ref_get(v___y_58_);
v_env_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_env_61_);
lean_dec(v___x_60_);
v___x_62_ = 0;
v_env_63_ = l_Lean_Environment_setRecordingDeps(v_env_61_, v___x_62_);
v___x_64_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_65_ = lean_st_ref_get(v___y_58_);
v_scopes_66_ = lean_ctor_get(v___x_65_, 2);
lean_inc(v_scopes_66_);
lean_dec(v___x_65_);
v___x_67_ = l_List_head_x21___redArg(v___x_64_, v_scopes_66_);
lean_dec(v_scopes_66_);
v_opts_68_ = lean_ctor_get(v___x_67_, 1);
lean_inc_ref(v_opts_68_);
lean_dec(v___x_67_);
v___x_69_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_70_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_71_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_71_, 0, v_env_63_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
lean_ctor_set(v___x_71_, 3, v_opts_68_);
v___x_72_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_msgData_57_);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_74_, v___y_75_);
lean_dec(v___y_75_);
return v_res_77_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_box(1);
v___x_79_ = l_Lean_MessageData_ofFormat(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2));
v___x_84_ = l_Lean_MessageData_ofFormat(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
return v_x_85_;
}
else
{
lean_object* v_head_87_; lean_object* v_tail_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_110_; 
v_head_87_ = lean_ctor_get(v_x_86_, 0);
v_tail_88_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_110_ == 0)
{
v___x_90_ = v_x_86_;
v_isShared_91_ = v_isSharedCheck_110_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_tail_88_);
lean_inc(v_head_87_);
lean_dec(v_x_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_110_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_before_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_108_; 
v_before_92_ = lean_ctor_get(v_head_87_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_head_87_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_head_87_, 1);
lean_dec(v_unused_109_);
v___x_94_ = v_head_87_;
v_isShared_95_ = v_isSharedCheck_108_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_before_92_);
lean_dec(v_head_87_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_108_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 7);
lean_ctor_set(v___x_94_, 1, v___x_96_);
lean_ctor_set(v___x_94_, 0, v_x_85_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_x_85_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_107_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 7);
lean_ctor_set(v___x_90_, 1, v___x_99_);
lean_ctor_set(v___x_90_, 0, v___x_98_);
v___x_101_ = v___x_90_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_106_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = l_Lean_MessageData_ofSyntax(v_before_92_);
v___x_103_ = l_Lean_indentD(v___x_102_);
v___x_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v_x_85_ = v___x_104_;
v_x_86_ = v_tail_88_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(lean_object* v_opts_111_, lean_object* v_opt_112_){
_start:
{
lean_object* v_name_113_; lean_object* v_defValue_114_; lean_object* v_map_115_; lean_object* v___x_116_; 
v_name_113_ = lean_ctor_get(v_opt_112_, 0);
v_defValue_114_ = lean_ctor_get(v_opt_112_, 1);
v_map_115_ = lean_ctor_get(v_opts_111_, 0);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_115_, v_name_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
uint8_t v___x_117_; 
v___x_117_ = lean_unbox(v_defValue_114_);
return v___x_117_;
}
else
{
lean_object* v_val_118_; 
v_val_118_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_116_, 1);
if (lean_obj_tag(v_val_118_) == 1)
{
uint8_t v_v_119_; 
v_v_119_ = lean_ctor_get_uint8(v_val_118_, 0);
lean_dec_ref_known(v_val_118_, 0);
return v_v_119_;
}
else
{
uint8_t v___x_120_; 
lean_dec(v_val_118_);
v___x_120_ = lean_unbox(v_defValue_114_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_opts_121_, lean_object* v_opt_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_121_, v_opt_122_);
lean_dec_ref(v_opt_122_);
lean_dec_ref(v_opts_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1));
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(lean_object* v_msgData_130_, lean_object* v_macroStack_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_scopes_136_; lean_object* v___x_137_; lean_object* v_opts_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_134_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_135_ = lean_st_ref_get(v___y_132_);
v_scopes_136_ = lean_ctor_get(v___x_135_, 2);
lean_inc(v_scopes_136_);
lean_dec(v___x_135_);
v___x_137_ = l_List_head_x21___redArg(v___x_134_, v_scopes_136_);
lean_dec(v_scopes_136_);
v_opts_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc_ref(v_opts_138_);
lean_dec(v___x_137_);
v___x_139_ = l_Lean_Elab_pp_macroStack;
v___x_140_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_138_, v___x_139_);
lean_dec_ref(v_opts_138_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_dec(v_macroStack_131_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_msgData_130_);
return v___x_141_;
}
else
{
if (lean_obj_tag(v_macroStack_131_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v_msgData_130_);
return v___x_142_;
}
else
{
lean_object* v_head_143_; lean_object* v_after_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_159_; 
v_head_143_ = lean_ctor_get(v_macroStack_131_, 0);
lean_inc(v_head_143_);
v_after_144_ = lean_ctor_get(v_head_143_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_head_143_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_head_143_, 0);
lean_dec(v_unused_160_);
v___x_146_ = v_head_143_;
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_after_144_);
lean_dec(v_head_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 7);
lean_ctor_set(v___x_146_, 1, v___x_148_);
lean_ctor_set(v___x_146_, 0, v_msgData_130_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_msgData_130_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_158_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_msgData_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_151_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_MessageData_ofSyntax(v_after_144_);
v___x_154_ = l_Lean_indentD(v___x_153_);
v_msgData_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_155_, 0, v___x_152_);
lean_ctor_set(v_msgData_155_, 1, v___x_154_);
v___x_156_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(v_msgData_155_, v_macroStack_131_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_161_, lean_object* v_macroStack_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_161_, v_macroStack_162_, v___y_163_);
lean_dec(v___y_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Elab_Command_getRef___redArg(v___y_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v_macroStack_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
v_macroStack_172_ = lean_ctor_get(v___y_167_, 4);
v___x_173_ = l_Lean_Elab_getBetterRef(v_a_171_, v_macroStack_172_);
lean_dec(v_a_171_);
v___x_174_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_166_, v___y_168_);
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref(v___x_174_);
lean_inc(v_macroStack_172_);
v___x_176_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_175_, v_macroStack_172_, v___y_168_);
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_173_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 1);
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v_msg_166_);
v_a_186_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_170_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_170_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object* v_ref_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Command_getRef___redArg(v___y_201_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v_fileName_206_; lean_object* v_fileMap_207_; lean_object* v_currRecDepth_208_; lean_object* v_cmdPos_209_; lean_object* v_macroStack_210_; lean_object* v_quotContext_x3f_211_; lean_object* v_currMacroScope_212_; lean_object* v_snap_x3f_213_; lean_object* v_cancelTk_x3f_214_; uint8_t v_suppressElabErrors_215_; lean_object* v_ref_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_204_, 1);
v_fileName_206_ = lean_ctor_get(v___y_201_, 0);
v_fileMap_207_ = lean_ctor_get(v___y_201_, 1);
v_currRecDepth_208_ = lean_ctor_get(v___y_201_, 2);
v_cmdPos_209_ = lean_ctor_get(v___y_201_, 3);
v_macroStack_210_ = lean_ctor_get(v___y_201_, 4);
v_quotContext_x3f_211_ = lean_ctor_get(v___y_201_, 5);
v_currMacroScope_212_ = lean_ctor_get(v___y_201_, 6);
v_snap_x3f_213_ = lean_ctor_get(v___y_201_, 8);
v_cancelTk_x3f_214_ = lean_ctor_get(v___y_201_, 9);
v_suppressElabErrors_215_ = lean_ctor_get_uint8(v___y_201_, sizeof(void*)*10);
v_ref_216_ = l_Lean_replaceRef(v_ref_199_, v_a_205_);
lean_dec(v_a_205_);
lean_inc(v_cancelTk_x3f_214_);
lean_inc(v_snap_x3f_213_);
lean_inc(v_currMacroScope_212_);
lean_inc(v_quotContext_x3f_211_);
lean_inc(v_macroStack_210_);
lean_inc(v_cmdPos_209_);
lean_inc(v_currRecDepth_208_);
lean_inc_ref(v_fileMap_207_);
lean_inc_ref(v_fileName_206_);
v___x_217_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_217_, 0, v_fileName_206_);
lean_ctor_set(v___x_217_, 1, v_fileMap_207_);
lean_ctor_set(v___x_217_, 2, v_currRecDepth_208_);
lean_ctor_set(v___x_217_, 3, v_cmdPos_209_);
lean_ctor_set(v___x_217_, 4, v_macroStack_210_);
lean_ctor_set(v___x_217_, 5, v_quotContext_x3f_211_);
lean_ctor_set(v___x_217_, 6, v_currMacroScope_212_);
lean_ctor_set(v___x_217_, 7, v_ref_216_);
lean_ctor_set(v___x_217_, 8, v_snap_x3f_213_);
lean_ctor_set(v___x_217_, 9, v_cancelTk_x3f_214_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*10, v_suppressElabErrors_215_);
v___x_218_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_200_, v___x_217_, v___y_202_);
lean_dec_ref_known(v___x_217_, 10);
return v___x_218_;
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v_msg_200_);
v_a_219_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_204_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_204_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v_ref_227_, lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_227_, v_msg_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v_ref_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object* v_k_236_, lean_object* v_as_237_, size_t v_sz_238_, size_t v_i_239_, lean_object* v_b_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_241_ == 0)
{
lean_dec(v_k_236_);
lean_inc_ref(v_b_240_);
return v_b_240_;
}
else
{
lean_object* v___x_242_; lean_object* v_a_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_242_ = lean_box(0);
v_a_243_ = lean_array_uget_borrowed(v_as_237_, v_i_239_);
lean_inc(v_a_243_);
v___x_244_ = l_Lean_Syntax_getKind(v_a_243_);
lean_inc(v_k_236_);
v___x_245_ = l_Lean_Elab_Command_checkRuleKind(v___x_244_, v_k_236_);
lean_dec(v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; size_t v___x_247_; size_t v___x_248_; 
v___x_246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_add(v_i_239_, v___x_247_);
v_i_239_ = v___x_248_;
v_b_240_ = v___x_246_;
goto _start;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_k_236_);
lean_inc(v_a_243_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_a_243_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_242_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object* v_k_253_, lean_object* v_as_254_, lean_object* v_sz_255_, lean_object* v_i_256_, lean_object* v_b_257_){
_start:
{
size_t v_sz_boxed_258_; size_t v_i_boxed_259_; lean_object* v_res_260_; 
v_sz_boxed_258_ = lean_unbox_usize(v_sz_255_);
lean_dec(v_sz_255_);
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_253_, v_as_254_, v_sz_boxed_258_, v_i_boxed_259_, v_b_257_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_as_254_);
return v_res_260_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0));
v___x_263_ = l_Lean_stringToMessageData(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12(void){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Array_mkArray0___redArg();
return v___x_280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object* v_k_288_, size_t v_sz_289_, size_t v_i_290_, lean_object* v_bs_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = lean_usize_dec_lt(v_i_290_, v_sz_289_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec(v_k_288_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v_bs_291_);
return v___x_296_;
}
else
{
lean_object* v_v_297_; lean_object* v___x_298_; lean_object* v_bs_x27_299_; lean_object* v_a_301_; lean_object* v___y_307_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_v_297_ = lean_array_uget(v_bs_291_, v_i_290_);
v___x_298_ = lean_unsigned_to_nat(0u);
v_bs_x27_299_ = lean_array_uset(v_bs_291_, v_i_290_, v___x_298_);
v___x_326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v_v_297_);
v___x_327_ = l_Lean_Syntax_isOfKind(v_v_297_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
lean_dec(v_v_297_);
v___x_328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_307_ = v___x_328_;
goto v___jp_306_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = l_Lean_Syntax_getArg(v_v_297_, v___x_329_);
lean_inc(v___x_330_);
v___x_331_ = l_Lean_Syntax_matchesNull(v___x_330_, v___x_329_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v___x_330_);
lean_dec(v_v_297_);
v___x_332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_307_ = v___x_332_;
goto v___jp_306_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___x_350_; lean_object* v_pat_351_; lean_object* v___y_353_; lean_object* v___y_354_; uint8_t v___x_406_; 
v___x_333_ = lean_box(0);
v___x_334_ = l_Lean_Syntax_getArg(v___x_330_, v___x_298_);
lean_dec(v___x_330_);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = l_Lean_Syntax_getArg(v_v_297_, v___x_335_);
v___x_350_ = l_Lean_Syntax_getArgs(v___x_334_);
lean_dec(v___x_334_);
v_pat_351_ = lean_array_get_borrowed(v___x_333_, v___x_350_, v___x_298_);
v___x_406_ = l_Lean_Syntax_isQuot(v_pat_351_);
if (v___x_406_ == 0)
{
if (v___x_331_ == 0)
{
v___y_353_ = v___y_292_;
v___y_354_ = v___y_293_;
goto v___jp_352_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
if (lean_obj_tag(v___x_407_) == 0)
{
lean_dec_ref_known(v___x_407_, 1);
v___y_353_ = v___y_292_;
v___y_354_ = v___y_293_;
goto v___jp_352_;
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v___x_350_);
lean_dec(v___x_336_);
lean_dec_ref(v_bs_x27_299_);
lean_dec(v_v_297_);
lean_dec(v_k_288_);
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
else
{
v___y_353_ = v___y_292_;
v___y_354_ = v___y_293_;
goto v___jp_352_;
}
v___jp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc_n(v___y_339_, 4);
v___x_341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_341_, 0, v___y_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
v___x_344_ = l_Array_append___redArg(v___x_343_, v___y_338_);
lean_dec_ref(v___y_338_);
v___x_345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_345_, 0, v___y_339_);
lean_ctor_set(v___x_345_, 1, v___x_342_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
v___x_346_ = l_Lean_Syntax_node1(v___y_339_, v___x_342_, v___x_345_);
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v___y_339_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = l_Lean_Syntax_node4(v___y_339_, v___x_326_, v___x_341_, v___x_346_, v___x_348_, v___x_336_);
v_a_301_ = v___x_349_;
goto v___jp_300_;
}
v___jp_352_:
{
lean_object* v_quoted_355_; lean_object* v_k_x27_356_; uint8_t v___x_357_; 
lean_inc(v_pat_351_);
v_quoted_355_ = l_Lean_Syntax_getQuotContent(v_pat_351_);
lean_inc(v_quoted_355_);
v_k_x27_356_ = l_Lean_Syntax_getKind(v_quoted_355_);
lean_inc(v_k_288_);
v___x_357_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_356_, v_k_288_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15));
v___x_359_ = lean_name_eq(v_k_x27_356_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_quoted_355_);
lean_dec_ref(v___x_350_);
lean_dec(v___x_336_);
v___x_360_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
v___x_361_ = l_Lean_MessageData_ofName(v_k_x27_356_);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_297_, v___x_364_, v___y_353_, v___y_354_);
lean_dec(v_v_297_);
v___y_307_ = v___x_365_;
goto v___jp_306_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; size_t v_sz_368_; size_t v___x_369_; lean_object* v___x_370_; lean_object* v_fst_371_; 
lean_dec(v_k_x27_356_);
v___x_366_ = l_Lean_Syntax_getArgs(v_quoted_355_);
lean_dec(v_quoted_355_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v_sz_368_ = lean_array_size(v___x_366_);
v___x_369_ = ((size_t)0ULL);
lean_inc(v_k_288_);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_288_, v___x_366_, v_sz_368_, v___x_369_, v___x_367_);
lean_dec_ref(v___x_366_);
v_fst_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_fst_371_);
lean_dec_ref(v___x_370_);
if (lean_obj_tag(v_fst_371_) == 0)
{
lean_dec_ref(v___x_350_);
lean_dec(v___x_336_);
v___y_318_ = v___y_353_;
v___y_319_ = v___y_354_;
goto v___jp_317_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v_fst_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v_fst_371_, 1);
if (lean_obj_tag(v_val_372_) == 0)
{
lean_dec_ref(v___x_350_);
lean_dec(v___x_336_);
v___y_318_ = v___y_353_;
v___y_319_ = v___y_354_;
goto v___jp_317_;
}
else
{
lean_object* v_val_373_; lean_object* v_pat_374_; lean_object* v_pats_375_; lean_object* v___x_376_; 
lean_dec(v_v_297_);
v_val_373_ = lean_ctor_get(v_val_372_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v_val_372_, 1);
lean_inc(v_pat_351_);
v_pat_374_ = l_Lean_Syntax_setArg(v_pat_351_, v___x_329_, v_val_373_);
v_pats_375_ = lean_array_set(v___x_350_, v___x_298_, v_pat_374_);
v___x_376_ = l_Lean_Elab_Command_getRef___redArg(v___y_353_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v___x_378_ = l_Lean_SourceInfo_fromRef(v_a_377_, v___x_357_);
lean_dec(v_a_377_);
v___x_379_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_353_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_quotContext_x3f_380_; 
lean_dec_ref_known(v___x_379_, 1);
v_quotContext_x3f_380_ = lean_ctor_get(v___y_353_, 5);
if (lean_obj_tag(v_quotContext_x3f_380_) == 0)
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_354_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_dec_ref_known(v___x_381_, 1);
v___y_338_ = v_pats_375_;
v___y_339_ = v___x_378_;
goto v___jp_337_;
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v___x_378_);
lean_dec_ref(v_pats_375_);
lean_dec(v___x_336_);
lean_dec_ref(v_bs_x27_299_);
lean_dec(v_k_288_);
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
v___y_338_ = v_pats_375_;
v___y_339_ = v___x_378_;
goto v___jp_337_;
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v___x_378_);
lean_dec_ref(v_pats_375_);
lean_dec(v___x_336_);
lean_dec_ref(v_bs_x27_299_);
lean_dec(v_k_288_);
v_a_390_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_379_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_379_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_pats_375_);
lean_dec(v___x_336_);
lean_dec_ref(v_bs_x27_299_);
lean_dec(v_k_288_);
v_a_398_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_376_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_376_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_356_);
lean_dec(v_quoted_355_);
lean_dec_ref(v___x_350_);
lean_dec(v___x_336_);
v_a_301_ = v_v_297_;
goto v___jp_300_;
}
}
}
}
v___jp_300_:
{
size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; 
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_add(v_i_290_, v___x_302_);
v___x_304_ = lean_array_uset(v_bs_x27_299_, v_i_290_, v_a_301_);
v_i_290_ = v___x_303_;
v_bs_291_ = v___x_304_;
goto _start;
}
v___jp_306_:
{
if (lean_obj_tag(v___y_307_) == 0)
{
lean_object* v_a_308_; 
v_a_308_ = lean_ctor_get(v___y_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___y_307_, 1);
v_a_301_ = v_a_308_;
goto v___jp_300_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_bs_x27_299_);
lean_dec(v_k_288_);
v_a_309_ = lean_ctor_get(v___y_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___y_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___y_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___y_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
v___jp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
lean_inc(v_k_288_);
v___x_321_ = l_Lean_MessageData_ofName(v_k_288_);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_297_, v___x_324_, v___y_318_, v___y_319_);
lean_dec(v_v_297_);
v___y_307_ = v___x_325_;
goto v___jp_306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(lean_object* v_k_416_, lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_bs_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v_sz_boxed_423_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_424_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_416_, v_sz_boxed_423_, v_i_boxed_424_, v_bs_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_431_ = l_String_toRawSubstring_x27(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_437_ = l_String_toRawSubstring_x27(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__18));
v___x_450_ = l_String_toRawSubstring_x27(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__25));
v___x_465_ = l_String_toRawSubstring_x27(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_492_, lean_object* v_attrs_x3f_493_, lean_object* v_attrKind_494_, lean_object* v_tk_495_, lean_object* v_k_496_, lean_object* v_alts_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
size_t v_sz_501_; size_t v___x_502_; lean_object* v___x_503_; 
v_sz_501_ = lean_array_size(v_alts_497_);
v___x_502_ = ((size_t)0ULL);
lean_inc(v_k_496_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_496_, v_sz_501_, v___x_502_, v_alts_497_, v_a_498_, v_a_499_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_688_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_688_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_688_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_688_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v_a_625_; lean_object* v___x_634_; 
v___x_634_ = l_Lean_Elab_Command_getRef___redArg(v_a_498_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; uint8_t v___x_636_; lean_object* v___y_638_; lean_object* v___x_658_; lean_object* v___x_677_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = 0;
v___x_658_ = l_Lean_SourceInfo_fromRef(v_a_635_, v___x_636_);
lean_dec(v_a_635_);
v___x_677_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_498_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_quotContext_x3f_678_; 
lean_dec_ref_known(v___x_677_, 1);
v_quotContext_x3f_678_ = lean_ctor_get(v_a_498_, 5);
if (lean_obj_tag(v_quotContext_x3f_678_) == 0)
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_499_);
lean_dec_ref(v___x_679_);
goto v___jp_659_;
}
else
{
goto v___jp_659_;
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v___x_658_);
lean_del_object(v___x_506_);
lean_dec(v_a_504_);
lean_dec(v_k_496_);
lean_dec(v_attrKind_494_);
lean_dec(v_doc_x3f_492_);
v_a_680_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_677_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_494_);
v___x_640_ = l_Lean_Elab_Command_getRef___redArg(v_a_498_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = l_Lean_SourceInfo_fromRef(v_a_641_, v___x_636_);
lean_dec(v_a_641_);
v___x_643_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_498_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_quotContext_x3f_644_; 
v_quotContext_x3f_644_ = lean_ctor_get(v_a_498_, 5);
if (lean_obj_tag(v_quotContext_x3f_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v_a_647_; 
v_a_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_643_, 1);
v___x_646_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_499_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v___y_621_ = v_a_645_;
v___y_622_ = v___y_638_;
v___y_623_ = v___x_639_;
v___y_624_ = v___x_642_;
v_a_625_ = v_a_647_;
goto v___jp_620_;
}
else
{
lean_object* v_a_648_; lean_object* v_val_649_; 
v_a_648_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_643_, 1);
v_val_649_ = lean_ctor_get(v_quotContext_x3f_644_, 0);
lean_inc(v_val_649_);
v___y_621_ = v_a_648_;
v___y_622_ = v___y_638_;
v___y_623_ = v___x_639_;
v___y_624_ = v___x_642_;
v_a_625_ = v_val_649_;
goto v___jp_620_;
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v___x_642_);
lean_dec(v___x_639_);
lean_dec_ref(v___y_638_);
lean_del_object(v___x_506_);
lean_dec(v_a_504_);
lean_dec(v_k_496_);
lean_dec(v_doc_x3f_492_);
v_a_650_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_643_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_643_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_dec(v___x_639_);
lean_dec_ref(v___y_638_);
lean_del_object(v___x_506_);
lean_dec(v_a_504_);
lean_dec(v_k_496_);
lean_dec(v_doc_x3f_492_);
return v___x_640_;
}
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__35));
v___x_661_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_662_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___x_658_, 2);
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_658_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
lean_inc(v_k_496_);
v___x_664_ = l_Lean_mkIdent(v_k_496_);
v___x_665_ = l_Lean_Syntax_node2(v___x_658_, v___x_662_, v___x_663_, v___x_664_);
lean_inc(v_attrKind_494_);
v___x_666_ = l_Lean_Syntax_node2(v___x_658_, v___x_660_, v_attrKind_494_, v___x_665_);
if (lean_obj_tag(v_attrs_x3f_493_) == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_mk_empty_array_with_capacity(v___x_668_);
v___x_670_ = lean_array_push(v___x_669_, v___x_666_);
v___x_671_ = l_Lean_Syntax_SepArray_ofElems(v___x_667_, v___x_670_);
lean_dec_ref(v___x_670_);
v___y_638_ = v___x_671_;
goto v___jp_637_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_val_672_ = lean_ctor_get(v_attrs_x3f_493_, 0);
v___x_673_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_674_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_672_);
v___x_675_ = lean_array_push(v___x_674_, v___x_666_);
v___x_676_ = l_Lean_Syntax_SepArray_ofElems(v___x_673_, v___x_675_);
lean_dec_ref(v___x_675_);
v___y_638_ = v___x_676_;
goto v___jp_637_;
}
}
}
else
{
lean_del_object(v___x_506_);
lean_dec(v_a_504_);
lean_dec(v_k_496_);
lean_dec(v_attrKind_494_);
lean_dec(v_doc_x3f_492_);
return v___x_634_;
}
v___jp_508_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
lean_inc_ref_n(v___y_510_, 3);
v___x_520_ = l_Array_append___redArg(v___y_510_, v___y_519_);
lean_dec_ref(v___y_519_);
lean_inc_n(v___y_516_, 8);
lean_inc_n(v___y_517_, 29);
v___x_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_521_, 0, v___y_517_);
lean_ctor_set(v___x_521_, 1, v___y_516_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_524_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_513_, 9);
v___x_525_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___y_517_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Array_append___redArg(v___y_510_, v___y_512_);
lean_dec_ref(v___y_512_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v___y_517_);
lean_ctor_set(v___x_529_, 1, v___y_516_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_517_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_Syntax_node3(v___y_517_, v___x_525_, v___x_527_, v___x_529_, v___x_531_);
v___x_533_ = l_Lean_Syntax_node1(v___y_517_, v___y_516_, v___x_532_);
lean_inc_ref(v___y_514_);
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_517_);
lean_ctor_set(v___x_534_, 1, v___y_514_);
v___x_535_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__4, &l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
v___x_536_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
lean_inc_n(v___y_509_, 3);
lean_inc_n(v___y_511_, 3);
v___x_537_ = l_Lean_addMacroScope(v___y_511_, v___x_536_, v___y_509_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_539_, 0, v___y_517_);
lean_ctor_set(v___x_539_, 1, v___x_535_);
lean_ctor_set(v___x_539_, 2, v___x_537_);
lean_ctor_set(v___x_539_, 3, v___x_538_);
v___x_540_ = 1;
v___x_541_ = l_Lean_mkIdentFrom(v_tk_495_, v_k_496_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node2(v___y_517_, v___y_516_, v___x_539_, v___x_541_);
v___x_543_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_544_, 0, v___y_517_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_546_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_547_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_548_ = l_Lean_addMacroScope(v___y_511_, v___x_547_, v___y_509_);
v___x_549_ = l_Lean_Name_mkStr2(v___y_513_, v___x_545_);
lean_inc(v___x_549_);
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_538_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___x_538_);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_550_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_554_, 0, v___y_517_);
lean_ctor_set(v___x_554_, 1, v___x_546_);
lean_ctor_set(v___x_554_, 2, v___x_548_);
lean_ctor_set(v___x_554_, 3, v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_517_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_558_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_557_);
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_517_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
v___x_560_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_561_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_560_);
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7));
v___x_563_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_562_);
v___x_564_ = l_Array_append___redArg(v___y_510_, v_a_504_);
lean_dec(v_a_504_);
v___x_565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
v___x_566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_566_, 0, v___y_517_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_568_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_567_);
v___x_569_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_517_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_Syntax_node1(v___y_517_, v___x_568_, v___x_570_);
v___x_572_ = l_Lean_Syntax_node1(v___y_517_, v___y_516_, v___x_571_);
v___x_573_ = l_Lean_Syntax_node1(v___y_517_, v___y_516_, v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v___y_517_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___x_577_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v___y_517_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_581_ = l_Lean_Name_mkStr4(v___y_513_, v___x_522_, v___x_523_, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__19, &l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
v___x_583_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
v___x_584_ = l_Lean_addMacroScope(v___y_511_, v___x_583_, v___y_509_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__24));
v___x_586_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_586_, 0, v___y_517_);
lean_ctor_set(v___x_586_, 1, v___x_582_);
lean_ctor_set(v___x_586_, 2, v___x_584_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
v___x_587_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__26, &l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
v___x_588_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__27));
v___x_589_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__28));
v___x_590_ = l_Lean_Name_mkStr4(v___y_513_, v___x_545_, v___x_588_, v___x_589_);
lean_inc_n(v___x_590_, 2);
v___x_591_ = l_Lean_addMacroScope(v___y_511_, v___x_590_, v___y_509_);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_538_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_590_);
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_538_);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_592_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v___y_517_);
lean_ctor_set(v___x_596_, 1, v___x_587_);
lean_ctor_set(v___x_596_, 2, v___x_591_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
v___x_597_ = l_Lean_Syntax_node1(v___y_517_, v___y_516_, v___x_596_);
v___x_598_ = l_Lean_Syntax_node2(v___y_517_, v___x_581_, v___x_586_, v___x_597_);
v___x_599_ = l_Lean_Syntax_node2(v___y_517_, v___x_577_, v___x_579_, v___x_598_);
v___x_600_ = l_Lean_Syntax_node4(v___y_517_, v___x_563_, v___x_566_, v___x_573_, v___x_575_, v___x_599_);
v___x_601_ = lean_array_push(v___x_564_, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v___y_517_);
lean_ctor_set(v___x_602_, 1, v___y_516_);
lean_ctor_set(v___x_602_, 2, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___y_517_, v___x_561_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node2(v___y_517_, v___x_558_, v___x_559_, v___x_603_);
v___x_605_ = lean_unsigned_to_nat(9u);
v___x_606_ = lean_mk_empty_array_with_capacity(v___x_605_);
v___x_607_ = lean_array_push(v___x_606_, v___x_521_);
v___x_608_ = lean_array_push(v___x_607_, v___x_533_);
v___x_609_ = lean_array_push(v___x_608_, v___y_515_);
v___x_610_ = lean_array_push(v___x_609_, v___x_534_);
v___x_611_ = lean_array_push(v___x_610_, v___x_542_);
v___x_612_ = lean_array_push(v___x_611_, v___x_544_);
v___x_613_ = lean_array_push(v___x_612_, v___x_554_);
v___x_614_ = lean_array_push(v___x_613_, v___x_556_);
v___x_615_ = lean_array_push(v___x_614_, v___x_604_);
lean_inc(v___y_518_);
v___x_616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_616_, 0, v___y_517_);
lean_ctor_set(v___x_616_, 1, v___y_518_);
lean_ctor_set(v___x_616_, 2, v___x_615_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_616_);
v___x_618_ = v___x_506_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
v___jp_620_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_627_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_628_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_492_) == 1)
{
lean_object* v_val_631_; lean_object* v___x_632_; 
v_val_631_ = lean_ctor_get(v_doc_x3f_492_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_doc_x3f_492_, 1);
v___x_632_ = l_Array_mkArray1___redArg(v_val_631_);
v___y_509_ = v___y_621_;
v___y_510_ = v___x_630_;
v___y_511_ = v_a_625_;
v___y_512_ = v___y_622_;
v___y_513_ = v___x_626_;
v___y_514_ = v___x_627_;
v___y_515_ = v___y_623_;
v___y_516_ = v___x_629_;
v___y_517_ = v___y_624_;
v___y_518_ = v___x_628_;
v___y_519_ = v___x_632_;
goto v___jp_508_;
}
else
{
lean_object* v___x_633_; 
lean_dec(v_doc_x3f_492_);
v___x_633_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_509_ = v___y_621_;
v___y_510_ = v___x_630_;
v___y_511_ = v_a_625_;
v___y_512_ = v___y_622_;
v___y_513_ = v___x_626_;
v___y_514_ = v___x_627_;
v___y_515_ = v___y_623_;
v___y_516_ = v___x_629_;
v___y_517_ = v___y_624_;
v___y_518_ = v___x_628_;
v___y_519_ = v___x_633_;
goto v___jp_508_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_k_496_);
lean_dec(v_attrKind_494_);
lean_dec(v_doc_x3f_492_);
v_a_689_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_503_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_503_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_697_, lean_object* v_attrs_x3f_698_, lean_object* v_attrKind_699_, lean_object* v_tk_700_, lean_object* v_k_701_, lean_object* v_alts_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_697_, v_attrs_x3f_698_, v_attrKind_699_, v_tk_700_, v_k_701_, v_alts_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_tk_700_);
lean_dec(v_attrs_x3f_698_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v_00_u03b1_707_, lean_object* v_ref_708_, lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_708_, v_msg_709_, v___y_710_, v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v_00_u03b1_714_, lean_object* v_ref_715_, lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v_00_u03b1_714_, v_ref_715_, v_msg_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v_ref_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object* v_msgData_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_721_, v___y_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* v_00_u03b1_731_, lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* v_00_u03b1_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_737_, v_msg_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object* v_msgData_743_, lean_object* v_macroStack_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_743_, v_macroStack_744_, v___y_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_749_, lean_object* v_macroStack_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_749_, v_macroStack_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object* v___y_755_, uint8_t v_isExporting_756_, lean_object* v_a_x3f_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_env_760_; lean_object* v_messages_761_; lean_object* v_scopes_762_; lean_object* v_usedQuotCtxts_763_; lean_object* v_nextMacroScope_764_; lean_object* v_maxRecDepth_765_; lean_object* v_ngen_766_; lean_object* v_auxDeclNGen_767_; lean_object* v_infoState_768_; lean_object* v_traceState_769_; lean_object* v_snapshotTasks_770_; lean_object* v_prevLinterStates_771_; lean_object* v_codeQualityEntryTasks_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v___x_759_ = lean_st_ref_take(v___y_755_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
v_messages_761_ = lean_ctor_get(v___x_759_, 1);
v_scopes_762_ = lean_ctor_get(v___x_759_, 2);
v_usedQuotCtxts_763_ = lean_ctor_get(v___x_759_, 3);
v_nextMacroScope_764_ = lean_ctor_get(v___x_759_, 4);
v_maxRecDepth_765_ = lean_ctor_get(v___x_759_, 5);
v_ngen_766_ = lean_ctor_get(v___x_759_, 6);
v_auxDeclNGen_767_ = lean_ctor_get(v___x_759_, 7);
v_infoState_768_ = lean_ctor_get(v___x_759_, 8);
v_traceState_769_ = lean_ctor_get(v___x_759_, 9);
v_snapshotTasks_770_ = lean_ctor_get(v___x_759_, 10);
v_prevLinterStates_771_ = lean_ctor_get(v___x_759_, 11);
v_codeQualityEntryTasks_772_ = lean_ctor_get(v___x_759_, 12);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v___x_759_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_codeQualityEntryTasks_772_);
lean_inc(v_prevLinterStates_771_);
lean_inc(v_snapshotTasks_770_);
lean_inc(v_traceState_769_);
lean_inc(v_infoState_768_);
lean_inc(v_auxDeclNGen_767_);
lean_inc(v_ngen_766_);
lean_inc(v_maxRecDepth_765_);
lean_inc(v_nextMacroScope_764_);
lean_inc(v_usedQuotCtxts_763_);
lean_inc(v_scopes_762_);
lean_inc(v_messages_761_);
lean_inc(v_env_760_);
lean_dec(v___x_759_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_776_ = lean_box(0);
v___x_777_ = l_Lean_Environment_setExporting(v_env_760_, v_isExporting_756_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_777_);
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_messages_761_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_scopes_762_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_usedQuotCtxts_763_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_nextMacroScope_764_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_maxRecDepth_765_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_ngen_766_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_auxDeclNGen_767_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_infoState_768_);
lean_ctor_set(v_reuseFailAlloc_782_, 9, v_traceState_769_);
lean_ctor_set(v_reuseFailAlloc_782_, 10, v_snapshotTasks_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 11, v_prevLinterStates_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 12, v_codeQualityEntryTasks_772_);
v___x_779_ = v_reuseFailAlloc_782_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_st_ref_put(v___y_755_, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_776_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(lean_object* v___y_784_, lean_object* v_isExporting_785_, lean_object* v_a_x3f_786_, lean_object* v___y_787_){
_start:
{
uint8_t v_isExporting_boxed_788_; lean_object* v_res_789_; 
v_isExporting_boxed_788_ = lean_unbox(v_isExporting_785_);
v_res_789_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_784_, v_isExporting_boxed_788_, v_a_x3f_786_);
lean_dec(v_a_x3f_786_);
lean_dec(v___y_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(lean_object* v_x_790_, uint8_t v_isExporting_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_env_796_; lean_object* v___x_797_; uint8_t v_isModule_798_; 
v___x_795_ = lean_st_ref_get(v___y_793_);
v_env_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref(v_env_796_);
lean_dec(v___x_795_);
v___x_797_ = l_Lean_Environment_header(v_env_796_);
v_isModule_798_ = lean_ctor_get_uint8(v___x_797_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_797_);
if (v_isModule_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_env_796_);
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
v___x_799_ = lean_apply_3(v_x_790_, v___y_792_, v___y_793_, lean_box(0));
return v___x_799_;
}
else
{
uint8_t v_isExporting_800_; 
v_isExporting_800_ = lean_ctor_get_uint8(v_env_796_, sizeof(void*)*13);
lean_dec_ref(v_env_796_);
if (v_isExporting_791_ == 0)
{
if (v_isExporting_800_ == 0)
{
lean_object* v___x_854_; 
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
v___x_854_ = lean_apply_3(v_x_790_, v___y_792_, v___y_793_, lean_box(0));
return v___x_854_;
}
else
{
goto v___jp_801_;
}
}
else
{
if (v_isExporting_800_ == 0)
{
goto v___jp_801_;
}
else
{
lean_object* v___x_855_; 
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
v___x_855_ = lean_apply_3(v_x_790_, v___y_792_, v___y_793_, lean_box(0));
return v___x_855_;
}
}
v___jp_801_:
{
lean_object* v___x_802_; lean_object* v_env_803_; lean_object* v_messages_804_; lean_object* v_scopes_805_; lean_object* v_usedQuotCtxts_806_; lean_object* v_nextMacroScope_807_; lean_object* v_maxRecDepth_808_; lean_object* v_ngen_809_; lean_object* v_auxDeclNGen_810_; lean_object* v_infoState_811_; lean_object* v_traceState_812_; lean_object* v_snapshotTasks_813_; lean_object* v_prevLinterStates_814_; lean_object* v_codeQualityEntryTasks_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_853_; 
v___x_802_ = lean_st_ref_take(v___y_793_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
v_messages_804_ = lean_ctor_get(v___x_802_, 1);
v_scopes_805_ = lean_ctor_get(v___x_802_, 2);
v_usedQuotCtxts_806_ = lean_ctor_get(v___x_802_, 3);
v_nextMacroScope_807_ = lean_ctor_get(v___x_802_, 4);
v_maxRecDepth_808_ = lean_ctor_get(v___x_802_, 5);
v_ngen_809_ = lean_ctor_get(v___x_802_, 6);
v_auxDeclNGen_810_ = lean_ctor_get(v___x_802_, 7);
v_infoState_811_ = lean_ctor_get(v___x_802_, 8);
v_traceState_812_ = lean_ctor_get(v___x_802_, 9);
v_snapshotTasks_813_ = lean_ctor_get(v___x_802_, 10);
v_prevLinterStates_814_ = lean_ctor_get(v___x_802_, 11);
v_codeQualityEntryTasks_815_ = lean_ctor_get(v___x_802_, 12);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_853_ == 0)
{
v___x_817_ = v___x_802_;
v_isShared_818_ = v_isSharedCheck_853_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_codeQualityEntryTasks_815_);
lean_inc(v_prevLinterStates_814_);
lean_inc(v_snapshotTasks_813_);
lean_inc(v_traceState_812_);
lean_inc(v_infoState_811_);
lean_inc(v_auxDeclNGen_810_);
lean_inc(v_ngen_809_);
lean_inc(v_maxRecDepth_808_);
lean_inc(v_nextMacroScope_807_);
lean_inc(v_usedQuotCtxts_806_);
lean_inc(v_scopes_805_);
lean_inc(v_messages_804_);
lean_inc(v_env_803_);
lean_dec(v___x_802_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_853_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_Environment_setExporting(v_env_803_, v_isExporting_791_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_messages_804_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_scopes_805_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_usedQuotCtxts_806_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v_nextMacroScope_807_);
lean_ctor_set(v_reuseFailAlloc_852_, 5, v_maxRecDepth_808_);
lean_ctor_set(v_reuseFailAlloc_852_, 6, v_ngen_809_);
lean_ctor_set(v_reuseFailAlloc_852_, 7, v_auxDeclNGen_810_);
lean_ctor_set(v_reuseFailAlloc_852_, 8, v_infoState_811_);
lean_ctor_set(v_reuseFailAlloc_852_, 9, v_traceState_812_);
lean_ctor_set(v_reuseFailAlloc_852_, 10, v_snapshotTasks_813_);
lean_ctor_set(v_reuseFailAlloc_852_, 11, v_prevLinterStates_814_);
lean_ctor_set(v_reuseFailAlloc_852_, 12, v_codeQualityEntryTasks_815_);
v___x_821_ = v_reuseFailAlloc_852_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v_r_823_; 
v___x_822_ = lean_st_ref_put(v___y_793_, v___x_821_);
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
v_r_823_ = lean_apply_3(v_x_790_, v___y_792_, v___y_793_, lean_box(0));
if (lean_obj_tag(v_r_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_840_; 
v_a_824_ = lean_ctor_get(v_r_823_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v_r_823_);
if (v_isSharedCheck_840_ == 0)
{
v___x_826_ = v_r_823_;
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v_r_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
lean_inc(v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 1);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_839_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v___x_830_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_793_, v_isExporting_800_, v___x_829_);
lean_dec_ref(v___x_829_);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_830_, 0);
lean_dec(v_unused_838_);
v___x_832_ = v___x_830_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_dec(v___x_830_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v_a_824_);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_824_);
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
else
{
lean_object* v_a_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_841_ = lean_ctor_get(v_r_823_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v_r_823_, 1);
v___x_842_ = lean_box(0);
v___x_843_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_793_, v_isExporting_800_, v___x_842_);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_843_, 0);
lean_dec(v_unused_851_);
v___x_845_ = v___x_843_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_dec(v___x_843_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 1);
lean_ctor_set(v___x_845_, 0, v_a_841_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_841_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v_x_856_, lean_object* v_isExporting_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
uint8_t v_isExporting_boxed_861_; lean_object* v_res_862_; 
v_isExporting_boxed_861_ = lean_unbox(v_isExporting_857_);
v_res_862_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_856_, v_isExporting_boxed_861_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_863_, lean_object* v_x_864_, uint8_t v_isExporting_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_864_, v_isExporting_865_, v___y_866_, v___y_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_870_, lean_object* v_x_871_, lean_object* v_isExporting_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v_isExporting_boxed_876_; lean_object* v_res_877_; 
v_isExporting_boxed_876_ = lean_unbox(v_isExporting_872_);
v_res_877_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_870_, v_x_871_, v_isExporting_boxed_876_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_878_, lean_object* v___x_879_, lean_object* v_doc_x3f_880_, lean_object* v_attrs_x3f_881_, lean_object* v_attrKind_882_, lean_object* v_tk_883_, lean_object* v_alts_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Elab_Command_getRef___redArg(v___y_885_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v_fileName_890_; lean_object* v_fileMap_891_; lean_object* v_currRecDepth_892_; lean_object* v_cmdPos_893_; lean_object* v_macroStack_894_; lean_object* v_quotContext_x3f_895_; lean_object* v_currMacroScope_896_; lean_object* v_snap_x3f_897_; lean_object* v_cancelTk_x3f_898_; uint8_t v_suppressElabErrors_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_918_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v_fileName_890_ = lean_ctor_get(v___y_885_, 0);
v_fileMap_891_ = lean_ctor_get(v___y_885_, 1);
v_currRecDepth_892_ = lean_ctor_get(v___y_885_, 2);
v_cmdPos_893_ = lean_ctor_get(v___y_885_, 3);
v_macroStack_894_ = lean_ctor_get(v___y_885_, 4);
v_quotContext_x3f_895_ = lean_ctor_get(v___y_885_, 5);
v_currMacroScope_896_ = lean_ctor_get(v___y_885_, 6);
v_snap_x3f_897_ = lean_ctor_get(v___y_885_, 8);
v_cancelTk_x3f_898_ = lean_ctor_get(v___y_885_, 9);
v_suppressElabErrors_899_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*10);
v_isSharedCheck_918_ = !lean_is_exclusive(v___y_885_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___y_885_, 7);
lean_dec(v_unused_919_);
v___x_901_ = v___y_885_;
v_isShared_902_ = v_isSharedCheck_918_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_cancelTk_x3f_898_);
lean_inc(v_snap_x3f_897_);
lean_inc(v_currMacroScope_896_);
lean_inc(v_quotContext_x3f_895_);
lean_inc(v_macroStack_894_);
lean_inc(v_cmdPos_893_);
lean_inc(v_currRecDepth_892_);
lean_inc(v_fileMap_891_);
lean_inc(v_fileName_890_);
lean_dec(v___y_885_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_918_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_ref_903_; lean_object* v___x_905_; 
v_ref_903_ = l_Lean_replaceRef(v___x_878_, v_a_889_);
lean_dec(v_a_889_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 7, v_ref_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_fileName_890_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_fileMap_891_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_currRecDepth_892_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_cmdPos_893_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_macroStack_894_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v_quotContext_x3f_895_);
lean_ctor_set(v_reuseFailAlloc_917_, 6, v_currMacroScope_896_);
lean_ctor_set(v_reuseFailAlloc_917_, 7, v_ref_903_);
lean_ctor_set(v_reuseFailAlloc_917_, 8, v_snap_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_917_, 9, v_cancelTk_x3f_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*10, v_suppressElabErrors_899_);
v___x_905_ = v_reuseFailAlloc_917_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_879_, v___x_905_, v___y_886_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v___x_908_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_880_, v_attrs_x3f_881_, v_attrKind_882_, v_tk_883_, v_a_907_, v_alts_884_, v___x_905_, v___y_886_);
lean_dec_ref(v___x_905_);
return v___x_908_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v_alts_884_);
lean_dec(v_attrKind_882_);
lean_dec(v_doc_x3f_880_);
v_a_909_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_906_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_885_);
lean_dec_ref(v_alts_884_);
lean_dec(v_attrKind_882_);
lean_dec(v_doc_x3f_880_);
lean_dec(v___x_879_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v_doc_x3f_922_, lean_object* v_attrs_x3f_923_, lean_object* v_attrKind_924_, lean_object* v_tk_925_, lean_object* v_alts_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_920_, v___x_921_, v_doc_x3f_922_, v_attrs_x3f_923_, v_attrKind_924_, v_tk_925_, v_alts_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec(v_tk_925_);
lean_dec(v_attrs_x3f_923_);
lean_dec(v___x_920_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v_attrKind_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v_attrs_x3f_939_, lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v___x_942_, lean_object* v_doc_x3f_943_, lean_object* v_kind_x3f_944_, lean_object* v_alts_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Elab_Command_getRef___redArg(v___y_946_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1027_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_1027_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1027_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___x_1016_; 
v___x_954_ = 0;
v___x_955_ = l_Lean_SourceInfo_fromRef(v_a_950_, v___x_954_);
lean_dec(v_a_950_);
v___x_1016_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_946_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_quotContext_x3f_1017_; 
lean_dec_ref_known(v___x_1016_, 1);
v_quotContext_x3f_1017_ = lean_ctor_get(v___y_946_, 5);
if (lean_obj_tag(v_quotContext_x3f_1017_) == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_947_);
lean_dec_ref(v___x_1018_);
goto v___jp_1010_;
}
else
{
goto v___jp_1010_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
lean_dec(v_kind_x3f_944_);
lean_dec(v_doc_x3f_943_);
lean_dec_ref(v___x_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_937_);
lean_dec(v_attrKind_936_);
lean_dec(v___x_935_);
lean_dec(v___x_934_);
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1016_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
v___jp_956_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_inc_ref_n(v___y_958_, 2);
v___x_963_ = l_Array_append___redArg(v___y_958_, v___y_962_);
lean_dec_ref(v___y_962_);
lean_inc_n(v___y_961_, 2);
lean_inc_n(v___x_955_, 3);
v___x_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_955_);
lean_ctor_set(v___x_964_, 1, v___y_961_);
lean_ctor_set(v___x_964_, 2, v___x_963_);
v___x_965_ = l_Array_append___redArg(v___y_958_, v_alts_945_);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_955_);
lean_ctor_set(v___x_966_, 1, v___y_961_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
v___x_967_ = l_Lean_Syntax_node1(v___x_955_, v___x_934_, v___x_966_);
v___x_968_ = l_Lean_Syntax_node6(v___x_955_, v___x_935_, v___y_959_, v___y_960_, v_attrKind_936_, v___y_957_, v___x_964_, v___x_967_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_968_);
v___x_970_ = v___x_952_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
v___jp_972_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_inc_ref(v___y_973_);
v___x_977_ = l_Array_append___redArg(v___y_973_, v___y_976_);
lean_dec_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_n(v___x_955_, 2);
v___x_978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_978_, 0, v___x_955_);
lean_ctor_set(v___x_978_, 1, v___y_975_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_955_);
lean_ctor_set(v___x_979_, 1, v___x_937_);
if (lean_obj_tag(v_kind_x3f_944_) == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___y_957_ = v___x_979_;
v___y_958_ = v___y_973_;
v___y_959_ = v___y_974_;
v___y_960_ = v___x_978_;
v___y_961_ = v___y_975_;
v___y_962_ = v___x_980_;
goto v___jp_956_;
}
else
{
lean_object* v_val_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_val_981_ = lean_ctor_get(v_kind_x3f_944_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_kind_x3f_944_, 1);
v___x_982_ = l_Lean_mkIdent(v_val_981_);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_955_, 4);
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_955_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_955_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_955_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_955_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Array_mkArray5___redArg(v___x_984_, v___x_986_, v___x_988_, v___x_982_, v___x_990_);
v___y_957_ = v___x_979_;
v___y_958_ = v___y_973_;
v___y_959_ = v___y_974_;
v___y_960_ = v___x_978_;
v___y_961_ = v___y_975_;
v___y_962_ = v___x_991_;
goto v___jp_956_;
}
}
v___jp_992_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_inc_ref(v___y_993_);
v___x_996_ = l_Array_append___redArg(v___y_993_, v___y_995_);
lean_dec_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc(v___x_955_);
v___x_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_997_, 0, v___x_955_);
lean_ctor_set(v___x_997_, 1, v___y_994_);
lean_ctor_set(v___x_997_, 2, v___x_996_);
if (lean_obj_tag(v_attrs_x3f_939_) == 1)
{
lean_object* v_val_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_val_998_ = lean_ctor_get(v_attrs_x3f_939_, 0);
v___x_999_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_1000_ = l_Lean_Name_mkStr4(v___x_940_, v___x_941_, v___x_942_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_n(v___x_955_, 4);
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_955_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_inc_ref(v___y_993_);
v___x_1003_ = l_Array_append___redArg(v___y_993_, v_val_998_);
lean_inc(v___y_994_);
v___x_1004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1004_, 0, v___x_955_);
lean_ctor_set(v___x_1004_, 1, v___y_994_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_955_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node3(v___x_955_, v___x_1000_, v___x_1002_, v___x_1004_, v___x_1006_);
v___x_1008_ = l_Array_mkArray1___redArg(v___x_1007_);
v___y_973_ = v___y_993_;
v___y_974_ = v___x_997_;
v___y_975_ = v___y_994_;
v___y_976_ = v___x_1008_;
goto v___jp_972_;
}
else
{
lean_object* v___x_1009_; 
lean_dec_ref(v___x_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
v___x_1009_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___y_973_ = v___y_993_;
v___y_974_ = v___x_997_;
v___y_975_ = v___y_994_;
v___y_976_ = v___x_1009_;
goto v___jp_972_;
}
}
v___jp_1010_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_943_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1014_; 
v_val_1013_ = lean_ctor_get(v_doc_x3f_943_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_doc_x3f_943_, 1);
v___x_1014_ = l_Array_mkArray1___redArg(v_val_1013_);
v___y_993_ = v___x_1012_;
v___y_994_ = v___x_1011_;
v___y_995_ = v___x_1014_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1015_; 
lean_dec(v_doc_x3f_943_);
v___x_1015_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___y_993_ = v___x_1012_;
v___y_994_ = v___x_1011_;
v___y_995_ = v___x_1015_;
goto v___jp_992_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_kind_x3f_944_);
lean_dec(v_doc_x3f_943_);
lean_dec_ref(v___x_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_937_);
lean_dec(v_attrKind_936_);
lean_dec(v___x_935_);
lean_dec(v___x_934_);
v_a_1028_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_949_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_949_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_attrKind_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_attrs_x3f_1041_, lean_object* v___x_1042_, lean_object* v___x_1043_, lean_object* v___x_1044_, lean_object* v_doc_x3f_1045_, lean_object* v_kind_x3f_1046_, lean_object* v_alts_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_1036_, v___x_1037_, v_attrKind_1038_, v___x_1039_, v___x_1040_, v_attrs_x3f_1041_, v___x_1042_, v___x_1043_, v___x_1044_, v_doc_x3f_1045_, v_kind_x3f_1046_, v_alts_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v_alts_1047_);
lean_dec(v_attrs_x3f_1041_);
lean_dec(v___x_1040_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___y_1109_; lean_object* v___y_1110_; uint8_t v___y_1111_; uint8_t v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1118_; lean_object* v___y_1119_; uint8_t v___y_1120_; uint8_t v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; uint8_t v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1136_; lean_object* v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1145_; lean_object* v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1148_; lean_object* v___y_1149_; uint8_t v___y_1150_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; 
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_1154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
lean_inc(v_stx_1104_);
v___x_1157_ = l_Lean_Syntax_isOfKind(v_stx_1104_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1223_; 
lean_dec(v_stx_1104_);
v___x_1223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v_a_1237_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1277_; lean_object* v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v_attrs_x3f_1362_; lean_object* v_doc_x3f_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1537_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1224_);
v___x_1538_ = l_Lean_Syntax_isNone(v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1537_);
v___x_1540_ = l_Lean_Syntax_matchesNull(v___x_1537_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_dec(v___x_1537_);
lean_dec(v_stx_1104_);
v___x_1541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1541_;
}
else
{
lean_object* v_doc_x3f_1542_; 
v_doc_x3f_1542_ = l_Lean_Syntax_getArg(v___x_1537_, v___x_1224_);
lean_dec(v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1542_);
v___x_1546_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1542_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_dec(v_doc_x3f_1542_);
lean_dec(v_stx_1104_);
v___x_1547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1547_;
}
else
{
goto v___jp_1543_;
}
}
else
{
goto v___jp_1543_;
}
v___jp_1543_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_doc_x3f_1542_);
v_doc_x3f_1521_ = v___x_1544_;
v___y_1522_ = v___y_1105_;
v___y_1523_ = v___y_1106_;
goto v___jp_1520_;
}
}
}
else
{
lean_object* v___x_1548_; 
lean_dec(v___x_1537_);
v___x_1548_ = lean_box(0);
v_doc_x3f_1521_ = v___x_1548_;
v___y_1522_ = v___y_1105_;
v___y_1523_ = v___y_1106_;
goto v___jp_1520_;
}
v___jp_1225_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_1239_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_1240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v___y_1236_) == 1)
{
lean_object* v_val_1241_; lean_object* v___x_1242_; 
v_val_1241_ = lean_ctor_get(v___y_1236_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v___y_1236_, 1);
v___x_1242_ = l_Array_mkArray1___redArg(v_val_1241_);
v___y_1159_ = v___y_1227_;
v___y_1160_ = v___y_1229_;
v___y_1161_ = v___y_1231_;
v___y_1162_ = v_a_1237_;
v___y_1163_ = v___y_1234_;
v___y_1164_ = v___y_1233_;
v___y_1165_ = v___x_1238_;
v___y_1166_ = v___y_1235_;
v___y_1167_ = v___x_1239_;
v___y_1168_ = v___x_1240_;
v___y_1169_ = v___y_1226_;
v___y_1170_ = v___y_1228_;
v___y_1171_ = v___y_1230_;
v___y_1172_ = v___y_1232_;
v___y_1173_ = v___x_1242_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1243_; 
lean_dec(v___y_1236_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_1159_ = v___y_1227_;
v___y_1160_ = v___y_1229_;
v___y_1161_ = v___y_1231_;
v___y_1162_ = v_a_1237_;
v___y_1163_ = v___y_1234_;
v___y_1164_ = v___y_1233_;
v___y_1165_ = v___x_1238_;
v___y_1166_ = v___y_1235_;
v___y_1167_ = v___x_1239_;
v___y_1168_ = v___x_1240_;
v___y_1169_ = v___y_1226_;
v___y_1170_ = v___y_1228_;
v___y_1171_ = v___y_1230_;
v___y_1172_ = v___y_1232_;
v___y_1173_ = v___x_1243_;
goto v___jp_1158_;
}
}
v___jp_1244_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_1255_);
v___x_1259_ = l_Lean_Elab_Command_getRef___redArg(v___y_1252_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = l_Lean_SourceInfo_fromRef(v_a_1260_, v___y_1247_);
lean_dec(v_a_1260_);
v___x_1262_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1252_);
lean_dec_ref(v___y_1252_);
if (lean_obj_tag(v___x_1262_) == 0)
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v_a_1265_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1246_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v___y_1226_ = v___y_1250_;
v___y_1227_ = v___x_1258_;
v___y_1228_ = v___y_1251_;
v___y_1229_ = v___y_1257_;
v___y_1230_ = v___y_1253_;
v___y_1231_ = v___y_1248_;
v___y_1232_ = v___y_1254_;
v___y_1233_ = v_a_1263_;
v___y_1234_ = v___x_1261_;
v___y_1235_ = v___y_1249_;
v___y_1236_ = v___y_1256_;
v_a_1237_ = v_a_1265_;
goto v___jp_1225_;
}
else
{
lean_object* v_a_1266_; lean_object* v_val_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1262_, 1);
v_val_1267_ = lean_ctor_get(v___y_1245_, 0);
lean_inc(v_val_1267_);
v___y_1226_ = v___y_1250_;
v___y_1227_ = v___x_1258_;
v___y_1228_ = v___y_1251_;
v___y_1229_ = v___y_1257_;
v___y_1230_ = v___y_1253_;
v___y_1231_ = v___y_1248_;
v___y_1232_ = v___y_1254_;
v___y_1233_ = v_a_1266_;
v___y_1234_ = v___x_1261_;
v___y_1235_ = v___y_1249_;
v___y_1236_ = v___y_1256_;
v_a_1237_ = v_val_1267_;
goto v___jp_1225_;
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v___x_1261_);
lean_dec(v___x_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
v_a_1268_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1262_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1262_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_dec(v___x_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
return v___x_1259_;
}
}
v___jp_1276_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
lean_inc_ref(v___y_1287_);
v___x_1293_ = l_Lean_Name_mkStr4(v___x_1153_, v___x_1154_, v___y_1287_, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___y_1285_, 2);
v___x_1296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1285_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
lean_inc(v___y_1282_);
v___x_1297_ = l_Lean_Syntax_node2(v___y_1285_, v___x_1295_, v___x_1296_, v___y_1282_);
lean_inc(v___y_1290_);
v___x_1298_ = l_Lean_Syntax_node2(v___y_1285_, v___x_1293_, v___y_1290_, v___x_1297_);
if (lean_obj_tag(v___y_1280_) == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1300_ = lean_mk_empty_array_with_capacity(v___y_1289_);
v___x_1301_ = lean_array_push(v___x_1300_, v___x_1298_);
v___x_1302_ = l_Lean_Syntax_SepArray_ofElems(v___x_1299_, v___x_1301_);
lean_dec_ref(v___x_1301_);
v___y_1245_ = v___y_1277_;
v___y_1246_ = v___y_1278_;
v___y_1247_ = v___y_1279_;
v___y_1248_ = v___y_1281_;
v___y_1249_ = v___y_1282_;
v___y_1250_ = v___y_1283_;
v___y_1251_ = v___y_1284_;
v___y_1252_ = v___y_1286_;
v___y_1253_ = v___y_1287_;
v___y_1254_ = v___y_1288_;
v___y_1255_ = v___y_1290_;
v___y_1256_ = v___y_1291_;
v___y_1257_ = v___x_1302_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_val_1303_ = lean_ctor_get(v___y_1280_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___y_1280_, 1);
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1305_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1303_);
lean_dec(v_val_1303_);
v___x_1306_ = lean_array_push(v___x_1305_, v___x_1298_);
v___x_1307_ = l_Lean_Syntax_SepArray_ofElems(v___x_1304_, v___x_1306_);
lean_dec_ref(v___x_1306_);
v___y_1245_ = v___y_1277_;
v___y_1246_ = v___y_1278_;
v___y_1247_ = v___y_1279_;
v___y_1248_ = v___y_1281_;
v___y_1249_ = v___y_1282_;
v___y_1250_ = v___y_1283_;
v___y_1251_ = v___y_1284_;
v___y_1252_ = v___y_1286_;
v___y_1253_ = v___y_1287_;
v___y_1254_ = v___y_1288_;
v___y_1255_ = v___y_1290_;
v___y_1256_ = v___y_1291_;
v___y_1257_ = v___x_1307_;
goto v___jp_1244_;
}
}
v___jp_1308_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1323_ = l_Lean_Syntax_getArg(v___y_1310_, v___y_1314_);
lean_dec(v___y_1310_);
v___x_1324_ = lean_mk_empty_array_with_capacity(v___y_1311_);
lean_inc(v___y_1319_);
v___x_1325_ = lean_array_push(v___x_1324_, v___y_1319_);
lean_inc(v___x_1323_);
v___x_1326_ = lean_array_push(v___x_1325_, v___x_1323_);
v___x_1327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1328_ = lean_box(2);
v___x_1329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1327_);
lean_ctor_set(v___x_1329_, 2, v___x_1326_);
v___x_1330_ = l_Lean_Elab_Command_getRef___redArg(v___y_1317_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_fileName_1332_; lean_object* v_fileMap_1333_; lean_object* v_currRecDepth_1334_; lean_object* v_cmdPos_1335_; lean_object* v_macroStack_1336_; lean_object* v_quotContext_x3f_1337_; lean_object* v_currMacroScope_1338_; lean_object* v_snap_x3f_1339_; lean_object* v_cancelTk_x3f_1340_; uint8_t v_suppressElabErrors_1341_; lean_object* v_ref_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v_fileName_1332_ = lean_ctor_get(v___y_1317_, 0);
v_fileMap_1333_ = lean_ctor_get(v___y_1317_, 1);
v_currRecDepth_1334_ = lean_ctor_get(v___y_1317_, 2);
v_cmdPos_1335_ = lean_ctor_get(v___y_1317_, 3);
v_macroStack_1336_ = lean_ctor_get(v___y_1317_, 4);
v_quotContext_x3f_1337_ = lean_ctor_get(v___y_1317_, 5);
v_currMacroScope_1338_ = lean_ctor_get(v___y_1317_, 6);
v_snap_x3f_1339_ = lean_ctor_get(v___y_1317_, 8);
v_cancelTk_x3f_1340_ = lean_ctor_get(v___y_1317_, 9);
v_suppressElabErrors_1341_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*10);
v_ref_1342_ = l_Lean_replaceRef(v___x_1329_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref_known(v___x_1329_, 3);
lean_inc(v_cancelTk_x3f_1340_);
lean_inc(v_snap_x3f_1339_);
lean_inc(v_currMacroScope_1338_);
lean_inc(v_quotContext_x3f_1337_);
lean_inc(v_macroStack_1336_);
lean_inc(v_cmdPos_1335_);
lean_inc(v_currRecDepth_1334_);
lean_inc_ref(v_fileMap_1333_);
lean_inc_ref(v_fileName_1332_);
v___x_1343_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1343_, 0, v_fileName_1332_);
lean_ctor_set(v___x_1343_, 1, v_fileMap_1333_);
lean_ctor_set(v___x_1343_, 2, v_currRecDepth_1334_);
lean_ctor_set(v___x_1343_, 3, v_cmdPos_1335_);
lean_ctor_set(v___x_1343_, 4, v_macroStack_1336_);
lean_ctor_set(v___x_1343_, 5, v_quotContext_x3f_1337_);
lean_ctor_set(v___x_1343_, 6, v_currMacroScope_1338_);
lean_ctor_set(v___x_1343_, 7, v_ref_1342_);
lean_ctor_set(v___x_1343_, 8, v_snap_x3f_1339_);
lean_ctor_set(v___x_1343_, 9, v_cancelTk_x3f_1340_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*10, v_suppressElabErrors_1341_);
v___x_1344_ = l_Lean_Elab_Command_getRef___redArg(v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = l_Lean_SourceInfo_fromRef(v_a_1345_, v___y_1312_);
lean_dec(v_a_1345_);
v___x_1347_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_dec_ref_known(v___x_1347_, 1);
if (lean_obj_tag(v_quotContext_x3f_1337_) == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1309_);
lean_dec_ref(v___x_1348_);
v___y_1277_ = v_quotContext_x3f_1337_;
v___y_1278_ = v___y_1309_;
v___y_1279_ = v___y_1312_;
v___y_1280_ = v___y_1313_;
v___y_1281_ = v___x_1327_;
v___y_1282_ = v___y_1315_;
v___y_1283_ = v___y_1316_;
v___y_1284_ = v___x_1323_;
v___y_1285_ = v___x_1346_;
v___y_1286_ = v___x_1343_;
v___y_1287_ = v___y_1318_;
v___y_1288_ = v___y_1319_;
v___y_1289_ = v___y_1320_;
v___y_1290_ = v___y_1322_;
v___y_1291_ = v___y_1321_;
goto v___jp_1276_;
}
else
{
v___y_1277_ = v_quotContext_x3f_1337_;
v___y_1278_ = v___y_1309_;
v___y_1279_ = v___y_1312_;
v___y_1280_ = v___y_1313_;
v___y_1281_ = v___x_1327_;
v___y_1282_ = v___y_1315_;
v___y_1283_ = v___y_1316_;
v___y_1284_ = v___x_1323_;
v___y_1285_ = v___x_1346_;
v___y_1286_ = v___x_1343_;
v___y_1287_ = v___y_1318_;
v___y_1288_ = v___y_1319_;
v___y_1289_ = v___y_1320_;
v___y_1290_ = v___y_1322_;
v___y_1291_ = v___y_1321_;
goto v___jp_1276_;
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v___x_1346_);
lean_dec_ref_known(v___x_1343_, 10);
lean_dec(v___x_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1313_);
v_a_1349_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1347_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1343_, 10);
lean_dec(v___x_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1313_);
return v___x_1344_;
}
}
else
{
lean_dec_ref_known(v___x_1329_, 3);
lean_dec(v___x_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1313_);
return v___x_1330_;
}
}
v___jp_1357_:
{
lean_object* v___x_1363_; lean_object* v_attrKind_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1363_ = lean_unsigned_to_nat(2u);
v_attrKind_1364_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_1366_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v_attrKind_1364_);
v___x_1367_ = l_Lean_Syntax_isOfKind(v_attrKind_1364_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec(v_attrKind_1364_);
lean_dec(v_attrs_x3f_1362_);
lean_dec(v___y_1360_);
lean_dec(v_stx_1104_);
v___x_1368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v_tk_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1369_ = lean_unsigned_to_nat(3u);
v_tk_1370_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1369_);
v___x_1371_ = lean_unsigned_to_nat(4u);
v___x_1372_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1371_);
lean_inc(v___x_1372_);
v___x_1373_ = l_Lean_Syntax_matchesNull(v___x_1372_, v___x_1224_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1372_);
v___x_1375_ = l_Lean_Syntax_matchesNull(v___x_1372_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec(v___x_1372_);
lean_dec(v_tk_1370_);
lean_dec(v_attrKind_1364_);
lean_dec(v_attrs_x3f_1362_);
lean_dec(v___y_1360_);
lean_dec(v_stx_1104_);
v___x_1376_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1374_);
lean_dec(v_stx_1104_);
v___x_1378_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1377_);
v___x_1379_ = l_Lean_Syntax_isOfKind(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec(v___x_1377_);
lean_dec(v___x_1372_);
lean_dec(v_tk_1370_);
lean_dec(v_attrKind_1364_);
lean_dec(v_attrs_x3f_1362_);
lean_dec(v___y_1360_);
v___x_1380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1380_;
}
else
{
lean_object* v_kind_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_kind_1381_ = l_Lean_Syntax_getArg(v___x_1372_, v___x_1369_);
lean_dec(v___x_1372_);
v___x_1382_ = l_Lean_Syntax_getArg(v___x_1377_, v___x_1224_);
lean_dec(v___x_1377_);
lean_inc(v___x_1382_);
v___x_1383_ = l_Lean_Syntax_matchesNull(v___x_1382_, v___y_1361_);
if (v___x_1383_ == 0)
{
lean_object* v_alts_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___f_1393_; 
v_alts_1384_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1386_ = lean_box(2);
lean_inc_ref(v_alts_1384_);
v___x_1387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___x_1385_);
lean_ctor_set(v___x_1387_, 2, v_alts_1384_);
v___x_1388_ = lean_mk_empty_array_with_capacity(v___x_1363_);
lean_inc(v_tk_1370_);
v___x_1389_ = lean_array_push(v___x_1388_, v_tk_1370_);
v___x_1390_ = lean_array_push(v___x_1389_, v___x_1387_);
v___x_1391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1386_);
lean_ctor_set(v___x_1391_, 1, v___x_1385_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
v___x_1392_ = l_Lean_TSyntax_getId(v_kind_1381_);
lean_dec(v_kind_1381_);
lean_inc(v_attrKind_1364_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1393_, 0, v___x_1391_);
lean_closure_set(v___f_1393_, 1, v___x_1392_);
lean_closure_set(v___f_1393_, 2, v___y_1360_);
lean_closure_set(v___f_1393_, 3, v_attrs_x3f_1362_);
lean_closure_set(v___f_1393_, 4, v_attrKind_1364_);
lean_closure_set(v___f_1393_, 5, v_tk_1370_);
lean_closure_set(v___f_1393_, 6, v_alts_1384_);
if (v___x_1367_ == 0)
{
lean_dec(v_attrKind_1364_);
v___y_1127_ = v___x_1383_;
v___y_1128_ = v___y_1359_;
v___y_1129_ = v___y_1358_;
v___y_1130_ = v___f_1393_;
v___y_1131_ = v___x_1379_;
v___y_1132_ = v___x_1367_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = l_Lean_Syntax_getArg(v_attrKind_1364_, v___x_1224_);
lean_dec(v_attrKind_1364_);
lean_inc(v___x_1394_);
v___x_1395_ = l_Lean_Syntax_matchesNull(v___x_1394_, v___y_1361_);
if (v___x_1395_ == 0)
{
lean_dec(v___x_1394_);
v___y_1127_ = v___x_1383_;
v___y_1128_ = v___y_1359_;
v___y_1129_ = v___y_1358_;
v___y_1130_ = v___f_1393_;
v___y_1131_ = v___x_1379_;
v___y_1132_ = v___x_1395_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = l_Lean_Syntax_getArg(v___x_1394_, v___x_1224_);
lean_dec(v___x_1394_);
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1398_ = l_Lean_Syntax_isOfKind(v___x_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
v___y_1127_ = v___x_1383_;
v___y_1128_ = v___y_1359_;
v___y_1129_ = v___y_1358_;
v___y_1130_ = v___f_1393_;
v___y_1131_ = v___x_1379_;
v___y_1132_ = v___x_1398_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1393_, v___x_1383_, v___y_1358_, v___y_1359_);
return v___x_1399_;
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_1224_);
v___x_1401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v___x_1400_);
v___x_1402_ = l_Lean_Syntax_isOfKind(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v_alts_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; 
lean_dec(v___x_1400_);
v_alts_1403_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1405_ = lean_box(2);
lean_inc_ref(v_alts_1403_);
v___x_1406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v_alts_1403_);
v___x_1407_ = lean_mk_empty_array_with_capacity(v___x_1363_);
lean_inc(v_tk_1370_);
v___x_1408_ = lean_array_push(v___x_1407_, v_tk_1370_);
v___x_1409_ = lean_array_push(v___x_1408_, v___x_1406_);
v___x_1410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1405_);
lean_ctor_set(v___x_1410_, 1, v___x_1404_);
lean_ctor_set(v___x_1410_, 2, v___x_1409_);
v___x_1411_ = l_Lean_TSyntax_getId(v_kind_1381_);
lean_dec(v_kind_1381_);
lean_inc(v_attrKind_1364_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1412_, 0, v___x_1410_);
lean_closure_set(v___f_1412_, 1, v___x_1411_);
lean_closure_set(v___f_1412_, 2, v___y_1360_);
lean_closure_set(v___f_1412_, 3, v_attrs_x3f_1362_);
lean_closure_set(v___f_1412_, 4, v_attrKind_1364_);
lean_closure_set(v___f_1412_, 5, v_tk_1370_);
lean_closure_set(v___f_1412_, 6, v_alts_1403_);
if (v___x_1367_ == 0)
{
lean_dec(v_attrKind_1364_);
v___y_1136_ = v___y_1359_;
v___y_1137_ = v___y_1358_;
v___y_1138_ = v___x_1383_;
v___y_1139_ = v___f_1412_;
v___y_1140_ = v___x_1402_;
v___y_1141_ = v___x_1367_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = l_Lean_Syntax_getArg(v_attrKind_1364_, v___x_1224_);
lean_dec(v_attrKind_1364_);
lean_inc(v___x_1413_);
v___x_1414_ = l_Lean_Syntax_matchesNull(v___x_1413_, v___y_1361_);
if (v___x_1414_ == 0)
{
lean_dec(v___x_1413_);
v___y_1136_ = v___y_1359_;
v___y_1137_ = v___y_1358_;
v___y_1138_ = v___x_1383_;
v___y_1139_ = v___f_1412_;
v___y_1140_ = v___x_1402_;
v___y_1141_ = v___x_1414_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1415_ = l_Lean_Syntax_getArg(v___x_1413_, v___x_1224_);
lean_dec(v___x_1413_);
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1417_ = l_Lean_Syntax_isOfKind(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
v___y_1136_ = v___y_1359_;
v___y_1137_ = v___y_1358_;
v___y_1138_ = v___x_1383_;
v___y_1139_ = v___f_1412_;
v___y_1140_ = v___x_1402_;
v___y_1141_ = v___x_1417_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1412_, v___x_1402_, v___y_1358_, v___y_1359_);
return v___x_1418_;
}
}
}
}
else
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = l_Lean_Syntax_getArg(v___x_1400_, v___y_1361_);
lean_inc(v___x_1419_);
v___x_1420_ = l_Lean_Syntax_matchesNull(v___x_1419_, v___y_1361_);
if (v___x_1420_ == 0)
{
lean_object* v_alts_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___f_1430_; 
lean_dec(v___x_1419_);
lean_dec(v___x_1400_);
v_alts_1421_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1423_ = lean_box(2);
lean_inc_ref(v_alts_1421_);
v___x_1424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___x_1422_);
lean_ctor_set(v___x_1424_, 2, v_alts_1421_);
v___x_1425_ = lean_mk_empty_array_with_capacity(v___x_1363_);
lean_inc(v_tk_1370_);
v___x_1426_ = lean_array_push(v___x_1425_, v_tk_1370_);
v___x_1427_ = lean_array_push(v___x_1426_, v___x_1424_);
v___x_1428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1423_);
lean_ctor_set(v___x_1428_, 1, v___x_1422_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
v___x_1429_ = l_Lean_TSyntax_getId(v_kind_1381_);
lean_dec(v_kind_1381_);
lean_inc(v_attrKind_1364_);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1430_, 0, v___x_1428_);
lean_closure_set(v___f_1430_, 1, v___x_1429_);
lean_closure_set(v___f_1430_, 2, v___y_1360_);
lean_closure_set(v___f_1430_, 3, v_attrs_x3f_1362_);
lean_closure_set(v___f_1430_, 4, v_attrKind_1364_);
lean_closure_set(v___f_1430_, 5, v_tk_1370_);
lean_closure_set(v___f_1430_, 6, v_alts_1421_);
if (v___x_1367_ == 0)
{
lean_dec(v_attrKind_1364_);
v___y_1118_ = v___y_1359_;
v___y_1119_ = v___y_1358_;
v___y_1120_ = v___x_1402_;
v___y_1121_ = v___x_1420_;
v___y_1122_ = v___f_1430_;
v___y_1123_ = v___x_1367_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = l_Lean_Syntax_getArg(v_attrKind_1364_, v___x_1224_);
lean_dec(v_attrKind_1364_);
lean_inc(v___x_1431_);
v___x_1432_ = l_Lean_Syntax_matchesNull(v___x_1431_, v___y_1361_);
if (v___x_1432_ == 0)
{
lean_dec(v___x_1431_);
v___y_1118_ = v___y_1359_;
v___y_1119_ = v___y_1358_;
v___y_1120_ = v___x_1402_;
v___y_1121_ = v___x_1420_;
v___y_1122_ = v___f_1430_;
v___y_1123_ = v___x_1432_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = l_Lean_Syntax_getArg(v___x_1431_, v___x_1224_);
lean_dec(v___x_1431_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1435_ = l_Lean_Syntax_isOfKind(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
v___y_1118_ = v___y_1359_;
v___y_1119_ = v___y_1358_;
v___y_1120_ = v___x_1402_;
v___y_1121_ = v___x_1420_;
v___y_1122_ = v___f_1430_;
v___y_1123_ = v___x_1435_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1430_, v___x_1420_, v___y_1358_, v___y_1359_);
return v___x_1436_;
}
}
}
}
else
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = l_Lean_Syntax_getArg(v___x_1419_, v___x_1224_);
lean_dec(v___x_1419_);
lean_inc(v___x_1437_);
v___x_1438_ = l_Lean_Syntax_matchesNull(v___x_1437_, v___y_1361_);
if (v___x_1438_ == 0)
{
lean_object* v_alts_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; 
lean_dec(v___x_1437_);
lean_dec(v___x_1400_);
v_alts_1439_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1441_ = lean_box(2);
lean_inc_ref(v_alts_1439_);
v___x_1442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v_alts_1439_);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1363_);
lean_inc(v_tk_1370_);
v___x_1444_ = lean_array_push(v___x_1443_, v_tk_1370_);
v___x_1445_ = lean_array_push(v___x_1444_, v___x_1442_);
v___x_1446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1441_);
lean_ctor_set(v___x_1446_, 1, v___x_1440_);
lean_ctor_set(v___x_1446_, 2, v___x_1445_);
v___x_1447_ = l_Lean_TSyntax_getId(v_kind_1381_);
lean_dec(v_kind_1381_);
lean_inc(v_attrKind_1364_);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1448_, 0, v___x_1446_);
lean_closure_set(v___f_1448_, 1, v___x_1447_);
lean_closure_set(v___f_1448_, 2, v___y_1360_);
lean_closure_set(v___f_1448_, 3, v_attrs_x3f_1362_);
lean_closure_set(v___f_1448_, 4, v_attrKind_1364_);
lean_closure_set(v___f_1448_, 5, v_tk_1370_);
lean_closure_set(v___f_1448_, 6, v_alts_1439_);
if (v___x_1367_ == 0)
{
lean_dec(v_attrKind_1364_);
v___y_1145_ = v___y_1359_;
v___y_1146_ = v___y_1358_;
v___y_1147_ = v___x_1438_;
v___y_1148_ = v___x_1420_;
v___y_1149_ = v___f_1448_;
v___y_1150_ = v___x_1367_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = l_Lean_Syntax_getArg(v_attrKind_1364_, v___x_1224_);
lean_dec(v_attrKind_1364_);
lean_inc(v___x_1449_);
v___x_1450_ = l_Lean_Syntax_matchesNull(v___x_1449_, v___y_1361_);
if (v___x_1450_ == 0)
{
lean_dec(v___x_1449_);
v___y_1145_ = v___y_1359_;
v___y_1146_ = v___y_1358_;
v___y_1147_ = v___x_1438_;
v___y_1148_ = v___x_1420_;
v___y_1149_ = v___f_1448_;
v___y_1150_ = v___x_1450_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1451_ = l_Lean_Syntax_getArg(v___x_1449_, v___x_1224_);
lean_dec(v___x_1449_);
v___x_1452_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1453_ = l_Lean_Syntax_isOfKind(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
v___y_1145_ = v___y_1359_;
v___y_1146_ = v___y_1358_;
v___y_1147_ = v___x_1438_;
v___y_1148_ = v___x_1420_;
v___y_1149_ = v___f_1448_;
v___y_1150_ = v___x_1453_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1448_, v___x_1438_, v___y_1358_, v___y_1359_);
return v___x_1454_;
}
}
}
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Syntax_getArg(v___x_1437_, v___x_1224_);
lean_dec(v___x_1437_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_1455_);
v___x_1457_ = l_Lean_Syntax_isOfKind(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v_alts_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; 
lean_dec(v___x_1455_);
lean_dec(v___x_1400_);
v_alts_1458_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1460_ = lean_box(2);
lean_inc_ref(v_alts_1458_);
v___x_1461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___x_1459_);
lean_ctor_set(v___x_1461_, 2, v_alts_1458_);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1363_);
lean_inc(v_tk_1370_);
v___x_1463_ = lean_array_push(v___x_1462_, v_tk_1370_);
v___x_1464_ = lean_array_push(v___x_1463_, v___x_1461_);
v___x_1465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1460_);
lean_ctor_set(v___x_1465_, 1, v___x_1459_);
lean_ctor_set(v___x_1465_, 2, v___x_1464_);
v___x_1466_ = l_Lean_TSyntax_getId(v_kind_1381_);
lean_dec(v_kind_1381_);
lean_inc(v_attrKind_1364_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1467_, 0, v___x_1465_);
lean_closure_set(v___f_1467_, 1, v___x_1466_);
lean_closure_set(v___f_1467_, 2, v___y_1360_);
lean_closure_set(v___f_1467_, 3, v_attrs_x3f_1362_);
lean_closure_set(v___f_1467_, 4, v_attrKind_1364_);
lean_closure_set(v___f_1467_, 5, v_tk_1370_);
lean_closure_set(v___f_1467_, 6, v_alts_1458_);
if (v___x_1367_ == 0)
{
lean_dec(v_attrKind_1364_);
v___y_1109_ = v___y_1359_;
v___y_1110_ = v___y_1358_;
v___y_1111_ = v___x_1438_;
v___y_1112_ = v___x_1373_;
v___y_1113_ = v___f_1467_;
v___y_1114_ = v___x_1367_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = l_Lean_Syntax_getArg(v_attrKind_1364_, v___x_1224_);
lean_dec(v_attrKind_1364_);
lean_inc(v___x_1468_);
v___x_1469_ = l_Lean_Syntax_matchesNull(v___x_1468_, v___y_1361_);
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
v___y_1109_ = v___y_1359_;
v___y_1110_ = v___y_1358_;
v___y_1111_ = v___x_1438_;
v___y_1112_ = v___x_1373_;
v___y_1113_ = v___f_1467_;
v___y_1114_ = v___x_1469_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_1224_);
lean_dec(v___x_1468_);
v___x_1471_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1472_ = l_Lean_Syntax_isOfKind(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
v___y_1109_ = v___y_1359_;
v___y_1110_ = v___y_1358_;
v___y_1111_ = v___x_1438_;
v___y_1112_ = v___x_1373_;
v___y_1113_ = v___f_1467_;
v___y_1114_ = v___x_1472_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1467_, v___x_1373_, v___y_1358_, v___y_1359_);
return v___x_1473_;
}
}
}
}
else
{
lean_dec(v___x_1382_);
v___y_1309_ = v___y_1359_;
v___y_1310_ = v___x_1400_;
v___y_1311_ = v___x_1363_;
v___y_1312_ = v___x_1373_;
v___y_1313_ = v_attrs_x3f_1362_;
v___y_1314_ = v___x_1369_;
v___y_1315_ = v_kind_1381_;
v___y_1316_ = v___x_1455_;
v___y_1317_ = v___y_1358_;
v___y_1318_ = v___x_1365_;
v___y_1319_ = v_tk_1370_;
v___y_1320_ = v___y_1361_;
v___y_1321_ = v___y_1360_;
v___y_1322_ = v_attrKind_1364_;
goto v___jp_1308_;
}
}
else
{
lean_dec(v___x_1382_);
v___y_1309_ = v___y_1359_;
v___y_1310_ = v___x_1400_;
v___y_1311_ = v___x_1363_;
v___y_1312_ = v___x_1373_;
v___y_1313_ = v_attrs_x3f_1362_;
v___y_1314_ = v___x_1369_;
v___y_1315_ = v_kind_1381_;
v___y_1316_ = v___x_1455_;
v___y_1317_ = v___y_1358_;
v___y_1318_ = v___x_1365_;
v___y_1319_ = v_tk_1370_;
v___y_1320_ = v___y_1361_;
v___y_1321_ = v___y_1360_;
v___y_1322_ = v_attrKind_1364_;
goto v___jp_1308_;
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
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
lean_dec(v___x_1372_);
v___x_1474_ = lean_unsigned_to_nat(5u);
v___x_1475_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1474_);
lean_dec(v_stx_1104_);
v___x_1476_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1475_);
v___x_1477_ = l_Lean_Syntax_isOfKind(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_dec(v___x_1475_);
lean_dec(v_tk_1370_);
lean_dec(v_attrKind_1364_);
lean_dec(v_attrs_x3f_1362_);
lean_dec(v___y_1360_);
v___x_1478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1478_;
}
else
{
lean_object* v___f_1479_; lean_object* v___x_1480_; lean_object* v_alts_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1479_, 0, v___x_1476_);
lean_closure_set(v___f_1479_, 1, v___x_1156_);
lean_closure_set(v___f_1479_, 2, v_attrKind_1364_);
lean_closure_set(v___f_1479_, 3, v___x_1155_);
lean_closure_set(v___f_1479_, 4, v___x_1224_);
lean_closure_set(v___f_1479_, 5, v_attrs_x3f_1362_);
lean_closure_set(v___f_1479_, 6, v___x_1153_);
lean_closure_set(v___f_1479_, 7, v___x_1154_);
lean_closure_set(v___f_1479_, 8, v___x_1365_);
lean_closure_set(v___f_1479_, 9, v___y_1360_);
v___x_1480_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1224_);
lean_dec(v___x_1475_);
v_alts_1481_ = l_Lean_Syntax_getArgs(v___x_1480_);
lean_dec(v___x_1480_);
v___x_1482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1483_ = lean_box(2);
lean_inc_ref(v_alts_1481_);
v___x_1484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v_alts_1481_);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1363_);
v___x_1486_ = lean_array_push(v___x_1485_, v_tk_1370_);
v___x_1487_ = lean_array_push(v___x_1486_, v___x_1484_);
v___x_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1483_);
lean_ctor_set(v___x_1488_, 1, v___x_1482_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
v___x_1489_ = l_Lean_Elab_Command_getRef___redArg(v___y_1358_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v_fileName_1491_; lean_object* v_fileMap_1492_; lean_object* v_currRecDepth_1493_; lean_object* v_cmdPos_1494_; lean_object* v_macroStack_1495_; lean_object* v_quotContext_x3f_1496_; lean_object* v_currMacroScope_1497_; lean_object* v_snap_x3f_1498_; lean_object* v_cancelTk_x3f_1499_; uint8_t v_suppressElabErrors_1500_; lean_object* v_ref_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_fileName_1491_ = lean_ctor_get(v___y_1358_, 0);
v_fileMap_1492_ = lean_ctor_get(v___y_1358_, 1);
v_currRecDepth_1493_ = lean_ctor_get(v___y_1358_, 2);
v_cmdPos_1494_ = lean_ctor_get(v___y_1358_, 3);
v_macroStack_1495_ = lean_ctor_get(v___y_1358_, 4);
v_quotContext_x3f_1496_ = lean_ctor_get(v___y_1358_, 5);
v_currMacroScope_1497_ = lean_ctor_get(v___y_1358_, 6);
v_snap_x3f_1498_ = lean_ctor_get(v___y_1358_, 8);
v_cancelTk_x3f_1499_ = lean_ctor_get(v___y_1358_, 9);
v_suppressElabErrors_1500_ = lean_ctor_get_uint8(v___y_1358_, sizeof(void*)*10);
v_ref_1501_ = l_Lean_replaceRef(v___x_1488_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref_known(v___x_1488_, 3);
lean_inc(v_cancelTk_x3f_1499_);
lean_inc(v_snap_x3f_1498_);
lean_inc(v_currMacroScope_1497_);
lean_inc(v_quotContext_x3f_1496_);
lean_inc(v_macroStack_1495_);
lean_inc(v_cmdPos_1494_);
lean_inc(v_currRecDepth_1493_);
lean_inc_ref(v_fileMap_1492_);
lean_inc_ref(v_fileName_1491_);
v___x_1502_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1502_, 0, v_fileName_1491_);
lean_ctor_set(v___x_1502_, 1, v_fileMap_1492_);
lean_ctor_set(v___x_1502_, 2, v_currRecDepth_1493_);
lean_ctor_set(v___x_1502_, 3, v_cmdPos_1494_);
lean_ctor_set(v___x_1502_, 4, v_macroStack_1495_);
lean_ctor_set(v___x_1502_, 5, v_quotContext_x3f_1496_);
lean_ctor_set(v___x_1502_, 6, v_currMacroScope_1497_);
lean_ctor_set(v___x_1502_, 7, v_ref_1501_);
lean_ctor_set(v___x_1502_, 8, v_snap_x3f_1498_);
lean_ctor_set(v___x_1502_, 9, v_cancelTk_x3f_1499_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*10, v_suppressElabErrors_1500_);
v___x_1503_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1481_, v___x_1155_, v___f_1479_, v___x_1502_, v___y_1359_);
lean_dec_ref_known(v___x_1502_, 10);
lean_dec_ref(v_alts_1481_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1503_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1503_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1488_, 3);
lean_dec_ref(v_alts_1481_);
lean_dec_ref(v___f_1479_);
return v___x_1489_;
}
}
}
}
}
v___jp_1520_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = l_Lean_Syntax_getArg(v_stx_1104_, v___x_1524_);
v___x_1526_ = l_Lean_Syntax_isNone(v___x_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
lean_inc(v___x_1525_);
v___x_1527_ = l_Lean_Syntax_matchesNull(v___x_1525_, v___x_1524_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_dec(v___x_1525_);
lean_dec(v_doc_x3f_1521_);
lean_dec(v_stx_1104_);
v___x_1528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = l_Lean_Syntax_getArg(v___x_1525_, v___x_1224_);
lean_dec(v___x_1525_);
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1529_);
v___x_1531_ = l_Lean_Syntax_isOfKind(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec(v___x_1529_);
lean_dec(v_doc_x3f_1521_);
lean_dec(v_stx_1104_);
v___x_1532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; lean_object* v_attrs_x3f_1534_; lean_object* v___x_1535_; 
v___x_1533_ = l_Lean_Syntax_getArg(v___x_1529_, v___x_1524_);
lean_dec(v___x_1529_);
v_attrs_x3f_1534_ = l_Lean_Syntax_getArgs(v___x_1533_);
lean_dec(v___x_1533_);
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_attrs_x3f_1534_);
v___y_1358_ = v___y_1522_;
v___y_1359_ = v___y_1523_;
v___y_1360_ = v_doc_x3f_1521_;
v___y_1361_ = v___x_1524_;
v_attrs_x3f_1362_ = v___x_1535_;
goto v___jp_1357_;
}
}
}
else
{
lean_object* v___x_1536_; 
lean_dec(v___x_1525_);
v___x_1536_ = lean_box(0);
v___y_1358_ = v___y_1522_;
v___y_1359_ = v___y_1523_;
v___y_1360_ = v_doc_x3f_1521_;
v___y_1361_ = v___x_1524_;
v_attrs_x3f_1362_ = v___x_1536_;
goto v___jp_1357_;
}
}
}
v___jp_1108_:
{
if (v___y_1114_ == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1113_, v___y_1111_, v___y_1110_, v___y_1109_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1113_, v___y_1112_, v___y_1110_, v___y_1109_);
return v___x_1116_;
}
}
v___jp_1117_:
{
if (v___y_1123_ == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1122_, v___y_1120_, v___y_1119_, v___y_1118_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1122_, v___y_1121_, v___y_1119_, v___y_1118_);
return v___x_1125_;
}
}
v___jp_1126_:
{
if (v___y_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1130_, v___y_1131_, v___y_1129_, v___y_1128_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1130_, v___y_1127_, v___y_1129_, v___y_1128_);
return v___x_1134_;
}
}
v___jp_1135_:
{
if (v___y_1141_ == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1139_, v___y_1138_, v___y_1137_, v___y_1136_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1139_, v___y_1140_, v___y_1137_, v___y_1136_);
return v___x_1143_;
}
}
v___jp_1144_:
{
if (v___y_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1149_, v___y_1148_, v___y_1146_, v___y_1145_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1149_, v___y_1147_, v___y_1146_, v___y_1145_);
return v___x_1152_;
}
}
v___jp_1158_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_inc_ref_n(v___y_1168_, 3);
v___x_1174_ = l_Array_append___redArg(v___y_1168_, v___y_1173_);
lean_dec_ref(v___y_1173_);
lean_inc_n(v___y_1161_, 6);
lean_inc_n(v___y_1163_, 17);
v___x_1175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1175_, 0, v___y_1163_);
lean_ctor_set(v___x_1175_, 1, v___y_1161_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_1171_, 2);
v___x_1177_ = l_Lean_Name_mkStr4(v___x_1153_, v___x_1154_, v___y_1171_, v___x_1176_);
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1163_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Array_append___redArg(v___y_1168_, v___y_1160_);
lean_dec_ref(v___y_1160_);
v___x_1181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1181_, 0, v___y_1163_);
lean_ctor_set(v___x_1181_, 1, v___y_1161_);
lean_ctor_set(v___x_1181_, 2, v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1163_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_node3(v___y_1163_, v___x_1177_, v___x_1179_, v___x_1181_, v___x_1183_);
v___x_1185_ = l_Lean_Syntax_node1(v___y_1163_, v___y_1161_, v___x_1184_);
lean_inc_ref(v___y_1165_);
v___x_1186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___y_1163_);
lean_ctor_set(v___x_1186_, 1, v___y_1165_);
v___x_1187_ = l_Lean_TSyntax_getId(v___y_1166_);
v___x_1188_ = l_Lean_mkIdentFrom(v___y_1172_, v___x_1187_, v___x_1157_);
lean_dec(v___y_1172_);
v___x_1189_ = l_Lean_Syntax_node2(v___y_1163_, v___y_1161_, v___x_1188_, v___y_1166_);
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_1191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___y_1163_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_1194_ = l_Lean_addMacroScope(v___y_1162_, v___x_1193_, v___y_1164_);
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_1196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1163_);
lean_ctor_set(v___x_1196_, 1, v___x_1192_);
lean_ctor_set(v___x_1196_, 2, v___x_1194_);
lean_ctor_set(v___x_1196_, 3, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_1198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___y_1163_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_1200_ = l_Lean_Name_mkStr4(v___x_1153_, v___x_1154_, v___y_1171_, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1163_);
lean_ctor_set(v___x_1201_, 1, v___x_1199_);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7));
v___x_1203_ = l_Lean_Name_mkStr4(v___x_1153_, v___x_1154_, v___y_1171_, v___x_1202_);
v___x_1204_ = l_Lean_Syntax_node1(v___y_1163_, v___y_1161_, v___y_1169_);
v___x_1205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1205_, 0, v___y_1163_);
lean_ctor_set(v___x_1205_, 1, v___y_1161_);
lean_ctor_set(v___x_1205_, 2, v___y_1168_);
v___x_1206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1163_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_Syntax_node4(v___y_1163_, v___x_1203_, v___x_1204_, v___x_1205_, v___x_1207_, v___y_1170_);
v___x_1209_ = l_Lean_Syntax_node2(v___y_1163_, v___x_1200_, v___x_1201_, v___x_1208_);
v___x_1210_ = lean_unsigned_to_nat(9u);
v___x_1211_ = lean_mk_empty_array_with_capacity(v___x_1210_);
v___x_1212_ = lean_array_push(v___x_1211_, v___x_1175_);
v___x_1213_ = lean_array_push(v___x_1212_, v___x_1185_);
v___x_1214_ = lean_array_push(v___x_1213_, v___y_1159_);
v___x_1215_ = lean_array_push(v___x_1214_, v___x_1186_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1189_);
v___x_1217_ = lean_array_push(v___x_1216_, v___x_1191_);
v___x_1218_ = lean_array_push(v___x_1217_, v___x_1196_);
v___x_1219_ = lean_array_push(v___x_1218_, v___x_1198_);
v___x_1220_ = lean_array_push(v___x_1219_, v___x_1209_);
lean_inc(v___y_1167_);
v___x_1221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1163_);
lean_ctor_set(v___x_1221_, 1, v___y_1167_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___f_1559_; lean_object* v___x_1560_; 
v___f_1559_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1560_ = l_Lean_Elab_Command_adaptExpander(v___f_1559_, v_a_1555_, v_a_1556_, v_a_1557_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Elab_Command_elabMacroRules(v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1573_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1576_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1577_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1573_, v___x_1574_, v___x_1575_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1608_ = l_Lean_addBuiltinDeclarationRanges(v___x_1606_, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1610_;
}
}
lean_object* runtime_initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MacroRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_MacroRules(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MacroRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_MacroRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_MacroRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_MacroRules(builtin);
}
#ifdef __cplusplus
}
#endif
